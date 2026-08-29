/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Fintype.Sort
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Currying of multilinear maps

We register isomorphisms corresponding to currying or uncurrying variables, transforming a
multilinear function `f` on `n+1` variables into a linear function taking values in multilinear
functions in `n` variables, and into a multilinear function in `n` variables taking values in linear
functions. These operations are called `f.curryLeft` and `f.curryRight` respectively
(with inverses `f.uncurryLeft` and `f.uncurryRight`). These operations induce linear equivalences
between spaces of multilinear functions in `n+1` variables and spaces of linear functions into
multilinear functions in `n` variables (resp. multilinear functions in `n` variables taking values
in linear functions), called respectively `multilinearCurryLeftEquiv` and
`multilinearCurryRightEquiv`.

-/

@[expose] public section

open Fin Function Finset Set

universe uR uS uι uι' v v' v₁ v₂ v₃

variable {R : Type uR} {S : Type uS} {ι : Type uι} {ι' : Type uι'} {n : Nat}
  {M : Fin n.succ -> Type v} {M₁ : ι -> Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

/-!
### Currying

We associate to a multilinear map in `n+1` variables (i.e., based on `Fin n.succ`) two
curried functions, named `f.curryLeft` (which is a linear map on `E 0` taking values
in multilinear maps in `n` variables) and `f.curryRight` (which is a multilinear map in `n`
variables taking values in linear maps on `E 0`). In both constructions, the variable that is
singled out is `0`, to take advantage of the operations `cons` and `tail` on `Fin n`.
The inverse operations are called `uncurryLeft` and `uncurryRight`.

We also register linear equiv versions of these correspondences, in
`multilinearCurryLeftEquiv` and `multilinearCurryRightEquiv`.
-/


open MultilinearMap

variable [CommSemiring R] [forall i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [forall i, Module R (M i)] [Module R M'] [Module R M₂]

/-! #### Left currying -/


/--
Definition of `LinearMap.uncurryLeft` / `LinearMap.uncurryLeft` 的定义

English:
definition LinearMap.uncurryLeft
  signature: (f : M 0 ->ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂)
  body: MultilinearMap.mk' (fun m => f (m 0) (tail m))
    (fun m i x y => by cases i using Fin.cases <;> simp [Ne.symm])
    (fun m i c x => by cases i using Fin.cases <;> simp [Ne.symm])

@[simp]

中文:
定义 LinearMap.uncurryLeft
  签名: (f : M 0 ->ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂)
  定义体: MultilinearMap.mk' (fun m => f (m 0) (tail m))
    (fun m i x y => by cases i using Fin.cases <;> simp [Ne.symm])
    (fun m i c x => by cases i using Fin.cases <;> simp [Ne.symm])

@[simp]

Depends on / 依赖: Fin.cases, MultilinearMap, MultilinearMap.mk, Ne.symm
-/
def LinearMap.uncurryLeft (f : M 0 ->ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂) :
    MultilinearMap R M M₂ :=
  MultilinearMap.mk' (fun m => f (m 0) (tail m))
    (fun m i x y => by cases i using Fin.cases <;> simp [Ne.symm])
    (fun m i c x => by cases i using Fin.cases <;> simp [Ne.symm])

@[simp]
/--
theorem `LinearMap.uncurryLeft_apply` / 定理 `LinearMap.uncurryLeft_apply`

English:
theorem LinearMap.uncurryLeft_apply
  statement: (f : M 0 ->ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂)
  proof: rfl

中文:
定理 LinearMap.uncurryLeft_apply
  结论: (f : M 0 ->ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂)
  证明: rfl
-/
theorem LinearMap.uncurryLeft_apply (f : M 0 ->ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂)
    (m : forall i, M i) : f.uncurryLeft m = f (m 0) (tail m) :=
  rfl

/--
Definition of `MultilinearMap.curryLeft` / `MultilinearMap.curryLeft` 的定义

English:
definition MultilinearMap.curryLeft
  signature: (f : MultilinearMap R M M₂)
  body: MultilinearMap.mk' fun m => f (cons x m)
  map_add' x y := by
    ext m
    exact cons_add f m x y
  map_smul' c x := by
    ext m
    exact cons_smul f m c x

@[simp]

中文:
定义 MultilinearMap.curryLeft
  签名: (f : MultilinearMap R M M₂)
  定义体: MultilinearMap.mk' fun m => f (cons x m)
  map_add' x y := by
    ext m
    exact cons_add f m x y
  map_smul' c x := by
    ext m
    exact cons_smul f m c x

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.mk
-/
def MultilinearMap.curryLeft (f : MultilinearMap R M M₂) :
    M 0 ->ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂ where
  toFun x := MultilinearMap.mk' fun m => f (cons x m)
  map_add' x y := by
    ext m
    exact cons_add f m x y
  map_smul' c x := by
    ext m
    exact cons_smul f m c x

@[simp]
/--
theorem `MultilinearMap.curryLeft_apply` / 定理 `MultilinearMap.curryLeft_apply`

English:
theorem MultilinearMap.curryLeft_apply
  statement: (f : MultilinearMap R M M₂) (x : M 0)
  proof: rfl

@[simp]

中文:
定理 MultilinearMap.curryLeft_apply
  结论: (f : MultilinearMap R M M₂) (x : M 0)
  证明: rfl

@[simp]
-/
theorem MultilinearMap.curryLeft_apply (f : MultilinearMap R M M₂) (x : M 0)
    (m : forall i : Fin n, M i.succ) : f.curryLeft x m = f (cons x m) :=
  rfl

@[simp]
/--
theorem `LinearMap.curry_uncurryLeft` / 定理 `LinearMap.curry_uncurryLeft`

English:
theorem LinearMap.curry_uncurryLeft
  statement: (f : M 0 ->ₗ[R] MultilinearMap R (fun i :
  proof: by
  rfl

@[simp]

中文:
定理 LinearMap.curry_uncurryLeft
  结论: (f : M 0 ->ₗ[R] MultilinearMap R (fun i :
  证明: by
  rfl

@[simp]
-/
theorem LinearMap.curry_uncurryLeft (f : M 0 ->ₗ[R] MultilinearMap R (fun i :
    Fin n => M i.succ) M₂) : f.uncurryLeft.curryLeft = f := by
  rfl

@[simp]
/--
theorem `MultilinearMap.uncurry_curryLeft` / 定理 `MultilinearMap.uncurry_curryLeft`

English:
theorem MultilinearMap.uncurry_curryLeft
  given: (f : MultilinearMap R M M₂)
  proof: by
  ext m
  simp

中文:
定理 MultilinearMap.uncurry_curryLeft
  条件: (f : MultilinearMap R M M₂)
  证明: by
  ext m
  simp
-/
theorem MultilinearMap.uncurry_curryLeft (f : MultilinearMap R M M₂) :
    f.curryLeft.uncurryLeft = f := by
  ext m
  simp

variable (R M M₂)

/-- The space of multilinear maps on `Π (i : Fin (n+1)), M i` is canonically isomorphic to
the space of linear maps from `M 0` to the space of multilinear maps on
`Π (i : Fin n), M i.succ`, by separating the first variable. We register this isomorphism as a
linear isomorphism in `multilinearCurryLeftEquiv R M M₂`.

The direct and inverse maps are given by `f.curryLeft` and `f.uncurryLeft`. Use these
unless you need the full framework of linear equivs. -/
@[simps]
/--
Definition of `multilinearCurryLeftEquiv` / `multilinearCurryLeftEquiv` 的定义

English:
definition multilinearCurryLeftEquiv
  signature: :
  body: MultilinearMap.curryLeft
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := LinearMap.uncurryLeft
  left_inv := MultilinearMap.uncurry_curryLeft
  right_inv := LinearMap.curry_uncurryLeft

中文:
定义 multilinearCurryLeftEquiv
  签名: :
  定义体: MultilinearMap.curryLeft
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := LinearMap.uncurryLeft
  left_inv := MultilinearMap.uncurry_curryLeft
  right_inv := LinearMap.curry_uncurryLeft

Depends on / 依赖: MultilinearMap, MultilinearMap.curryLeft, curryLeft
-/
def multilinearCurryLeftEquiv :
    MultilinearMap R M M₂ ≃ₗ[R] (M 0 ->ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂) where
  toFun := MultilinearMap.curryLeft
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := LinearMap.uncurryLeft
  left_inv := MultilinearMap.uncurry_curryLeft
  right_inv := LinearMap.curry_uncurryLeft

variable {R M M₂}

/-! #### Right currying -/

/--
Definition of `MultilinearMap.uncurryRight` / `MultilinearMap.uncurryRight` 的定义

English:
definition MultilinearMap.uncurryRight
  body: MultilinearMap.mk' (fun m => f (init m) (m (last n)))
    (fun m i x y => by cases i using Fin.lastCases <;> simp [Ne.symm])
    (fun m i c x => by cases i using Fin.lastCases <;> simp [Ne.symm])

@[simp]

中文:
定义 MultilinearMap.uncurryRight
  定义体: MultilinearMap.mk' (fun m => f (init m) (m (last n)))
    (fun m i x y => by cases i using Fin.lastCases <;> simp [Ne.symm])
    (fun m i c x => by cases i using Fin.lastCases <;> simp [Ne.symm])

@[simp]

Depends on / 依赖: Fin.lastCases, MultilinearMap, MultilinearMap.mk, Ne.symm, lastCases
-/
def MultilinearMap.uncurryRight
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) ->ₗ[R] M₂)) :
    MultilinearMap R M M₂ :=
  MultilinearMap.mk' (fun m => f (init m) (m (last n)))
    (fun m i x y => by cases i using Fin.lastCases <;> simp [Ne.symm])
    (fun m i c x => by cases i using Fin.lastCases <;> simp [Ne.symm])

@[simp]
/--
theorem `MultilinearMap.uncurryRight_apply` / 定理 `MultilinearMap.uncurryRight_apply`

English:
theorem MultilinearMap.uncurryRight_apply
  proof: rfl

中文:
定理 MultilinearMap.uncurryRight_apply
  证明: rfl
-/
theorem MultilinearMap.uncurryRight_apply
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) ->ₗ[R] M₂))
    (m : forall i, M i) : f.uncurryRight m = f (init m) (m (last n)) :=
  rfl

/--
Definition of `MultilinearMap.curryRight` / `MultilinearMap.curryRight` 的定义

English:
definition MultilinearMap.curryRight
  signature: (f : MultilinearMap R M M₂)
  body: MultilinearMap.mk' fun m =>
    { toFun := fun x => f (snoc m x)
      map_add' := fun x y => by simp_rw [f.snoc_add]
      map_smul' := fun c x => by simp only [f.snoc_smul, RingHom.id_apply] }

@[simp]

中文:
定义 MultilinearMap.curryRight
  签名: (f : MultilinearMap R M M₂)
  定义体: MultilinearMap.mk' fun m =>
    { toFun := fun x => f (snoc m x)
      map_add' := fun x y => by simp_rw [f.snoc_add]
      map_smul' := fun c x => by simp only [f.snoc_smul, RingHom.id_apply] }

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.mk, RingHom, RingHom.id_apply, f.snoc_add, f.snoc_smul, id_apply, map_add, map_smul, simp_rw, snoc_add, snoc_smul
-/
def MultilinearMap.curryRight (f : MultilinearMap R M M₂) :
    MultilinearMap R (fun i : Fin n => M (Fin.castSucc i)) (M (last n) ->ₗ[R] M₂) :=
  MultilinearMap.mk' fun m =>
    { toFun := fun x => f (snoc m x)
      map_add' := fun x y => by simp_rw [f.snoc_add]
      map_smul' := fun c x => by simp only [f.snoc_smul, RingHom.id_apply] }

@[simp]
/--
theorem `MultilinearMap.curryRight_apply` / 定理 `MultilinearMap.curryRight_apply`

English:
theorem MultilinearMap.curryRight_apply
  statement: (f : MultilinearMap R M M₂)
  proof: rfl

@[simp]

中文:
定理 MultilinearMap.curryRight_apply
  结论: (f : MultilinearMap R M M₂)
  证明: rfl

@[simp]
-/
theorem MultilinearMap.curryRight_apply (f : MultilinearMap R M M₂)
    (m : forall i : Fin n, M (castSucc i)) (x : M (last n)) : f.curryRight m x = f (snoc m x) :=
  rfl

@[simp]
/--
theorem `MultilinearMap.curry_uncurryRight` / 定理 `MultilinearMap.curry_uncurryRight`

English:
theorem MultilinearMap.curry_uncurryRight
  proof: by
  ext m x
  simp only [snoc_last, MultilinearMap.curryRight_apply, MultilinearMap.uncurryRight_apply]
  rw [init_snoc]

@[simp]

中文:
定理 MultilinearMap.curry_uncurryRight
  证明: by
  ext m x
  simp only [snoc_last, MultilinearMap.curryRight_apply, MultilinearMap.uncurryRight_apply]
  rw [init_snoc]

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.curryRight_apply, MultilinearMap.uncurryRight_apply, curryRight_apply, init_snoc, snoc_last, uncurryRight_apply
-/
theorem MultilinearMap.curry_uncurryRight
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) ->ₗ[R] M₂)) :
    f.uncurryRight.curryRight = f := by
  ext m x
  simp only [snoc_last, MultilinearMap.curryRight_apply, MultilinearMap.uncurryRight_apply]
  rw [init_snoc]

@[simp]
/--
theorem `MultilinearMap.uncurry_curryRight` / 定理 `MultilinearMap.uncurry_curryRight`

English:
theorem MultilinearMap.uncurry_curryRight
  given: (f : MultilinearMap R M M₂)
  proof: by
  ext m
  simp

中文:
定理 MultilinearMap.uncurry_curryRight
  条件: (f : MultilinearMap R M M₂)
  证明: by
  ext m
  simp
-/
theorem MultilinearMap.uncurry_curryRight (f : MultilinearMap R M M₂) :
    f.curryRight.uncurryRight = f := by
  ext m
  simp

variable (R M M₂)

/--
Definition of `multilinearCurryRightEquiv` / `multilinearCurryRightEquiv` 的定义

English:
definition multilinearCurryRightEquiv
  signature: :
  body: MultilinearMap.curryRight
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := MultilinearMap.uncurryRight
  left_inv := MultilinearMap.uncurry_curryRight
  right_inv := MultilinearMap.curry_uncurryRight

中文:
定义 multilinearCurryRightEquiv
  签名: :
  定义体: MultilinearMap.curryRight
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := MultilinearMap.uncurryRight
  left_inv := MultilinearMap.uncurry_curryRight
  right_inv := MultilinearMap.curry_uncurryRight

Depends on / 依赖: MultilinearMap, MultilinearMap.curryRight, curryRight
-/
def multilinearCurryRightEquiv :
    MultilinearMap R M M₂ ≃ₗ[R]
      MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) ->ₗ[R] M₂) where
  toFun := MultilinearMap.curryRight
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := MultilinearMap.uncurryRight
  left_inv := MultilinearMap.uncurry_curryRight
  right_inv := MultilinearMap.curry_uncurryRight

variable {R M M₂}

/-- Given a linear map from `M p` to the space of multilinear maps
in `n` variables `M 0`, ..., `M n` with `M p` removed,
returns a multilinear map in all `n + 1` variables. -/
@[simps!]
/--
Definition of `LinearMap.uncurryMid` / `LinearMap.uncurryMid` 的定义

English:
definition LinearMap.uncurryMid
  signature: (p : Fin (n + 1))
  body: .mk' (fun m => f (m p) (p.removeNth m))
    (fun m i x y => by cases i using Fin.succAboveCases p <;> simp)
    (fun m i x y => by cases i using Fin.succAboveCases p <;> simp)

中文:
定义 LinearMap.uncurryMid
  签名: (p : Fin (n + 1))
  定义体: .mk' (fun m => f (m p) (p.removeNth m))
    (fun m i x y => by cases i using Fin.succAboveCases p <;> simp)
    (fun m i x y => by cases i using Fin.succAboveCases p <;> simp)

Depends on / 依赖: Fin.succAboveCases, p.removeNth, removeNth, succAboveCases
-/
def LinearMap.uncurryMid (p : Fin (n + 1))
    (f : M p ->ₗ[R] MultilinearMap R (fun i => M (p.succAbove i)) M₂) : MultilinearMap R M M₂ :=
  .mk' (fun m => f (m p) (p.removeNth m))
    (fun m i x y => by cases i using Fin.succAboveCases p <;> simp)
    (fun m i x y => by cases i using Fin.succAboveCases p <;> simp)

/-- Interpret a multilinear map in `n + 1` variables
as a linear map in `p`th variable with values in the multilinear maps in the other variables. -/
@[simps!]
/--
Definition of `MultilinearMap.curryMid` / `MultilinearMap.curryMid` 的定义

English:
definition MultilinearMap.curryMid
  signature: (p : Fin (n + 1)) (f : MultilinearMap R M M₂)
  body: .mk' fun m => f (p.insertNth x m)
  map_add' x y := by ext; simp [map_insertNth_add]
  map_smul' c x := by ext; simp [map_insertNth_smul]

@[simp]

中文:
定义 MultilinearMap.curryMid
  签名: (p : Fin (n + 1)) (f : MultilinearMap R M M₂)
  定义体: .mk' fun m => f (p.insertNth x m)
  map_add' x y := by ext; simp [map_insertNth_add]
  map_smul' c x := by ext; simp [map_insertNth_smul]

@[simp]

Depends on / 依赖: insertNth, p.insertNth
-/
def MultilinearMap.curryMid (p : Fin (n + 1)) (f : MultilinearMap R M M₂) :
    M p ->ₗ[R] MultilinearMap R (fun i => M (p.succAbove i)) M₂ where
  toFun x := .mk' fun m => f (p.insertNth x m)
  map_add' x y := by ext; simp [map_insertNth_add]
  map_smul' c x := by ext; simp [map_insertNth_smul]

@[simp]
/--
theorem `LinearMap.curryMid_uncurryMid` / 定理 `LinearMap.curryMid_uncurryMid`

English:
theorem LinearMap.curryMid_uncurryMid
  statement: (i : Fin (n + 1))
  proof: by ext; simp

@[simp]

中文:
定理 LinearMap.curryMid_uncurryMid
  结论: (i : Fin (n + 1))
  证明: by ext; simp

@[simp]
-/
theorem LinearMap.curryMid_uncurryMid (i : Fin (n + 1))
    (f : M i ->ₗ[R] MultilinearMap R (fun j => M (i.succAbove j)) M₂) :
    (f.uncurryMid i).curryMid i = f := by ext; simp

@[simp]
/--
theorem `MultilinearMap.uncurryMid_curryMid` / 定理 `MultilinearMap.uncurryMid_curryMid`

English:
theorem MultilinearMap.uncurryMid_curryMid
  given: (i : Fin (n + 1)) (f : MultilinearMap R M M₂)
  proof: by ext; simp

中文:
定理 MultilinearMap.uncurryMid_curryMid
  条件: (i : Fin (n + 1)) (f : MultilinearMap R M M₂)
  证明: by ext; simp
-/
theorem MultilinearMap.uncurryMid_curryMid (i : Fin (n + 1)) (f : MultilinearMap R M M₂) :
    (f.curryMid i).uncurryMid i = f := by ext; simp

variable (R M M₂)

/-- `MultilinearMap.curryMid` as a linear equivalence. -/
@[simps]
/--
Definition of `MultilinearMap.curryMidLinearEquiv` / `MultilinearMap.curryMidLinearEquiv` 的定义

English:
definition MultilinearMap.curryMidLinearEquiv
  signature: (p : Fin (n + 1))
  body: MultilinearMap.curryMid p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := LinearMap.uncurryMid p
  left_inv := MultilinearMap.uncurryMid_curryMid p
  right_inv := LinearMap.curryMid_uncurryMid p

中文:
定义 MultilinearMap.curryMidLinearEquiv
  签名: (p : Fin (n + 1))
  定义体: MultilinearMap.curryMid p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := LinearMap.uncurryMid p
  left_inv := MultilinearMap.uncurryMid_curryMid p
  right_inv := LinearMap.curryMid_uncurryMid p

Depends on / 依赖: MultilinearMap, MultilinearMap.curryMid, curryMid
-/
def MultilinearMap.curryMidLinearEquiv (p : Fin (n + 1)) :
    MultilinearMap R M M₂ ≃ₗ[R] M p ->ₗ[R] MultilinearMap R (fun i => M (p.succAbove i)) M₂ where
  toFun := MultilinearMap.curryMid p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := LinearMap.uncurryMid p
  left_inv := MultilinearMap.uncurryMid_curryMid p
  right_inv := LinearMap.curryMid_uncurryMid p

namespace MultilinearMap

variable {R M₂} {N : (ι oplus ι') -> Type*}
  [forall i, AddCommMonoid (N i)] [forall i, Module R (N i)]

/--
Definition of `currySum` / `currySum` 的定义

English:
definition currySum
  signature: (f : MultilinearMap R N M₂)
  body: { toFun v := f (Sum.rec u v)
      map_update_add' := by let := Classical.decEq ι; simp
      map_update_smul' := by let := Classical.decEq ι; simp }
  map_update_add' u i x y :=
    ext fun _ => by let := Classical.decEq ι'; simp
  map_update_smul' u i c x :=
    ext fun _ => by let := Classical.de

中文:
定义 currySum
  签名: (f : MultilinearMap R N M₂)
  定义体: { toFun v := f (Sum.rec u v)
      map_update_add' := by let := Classical.decEq ι; simp
      map_update_smul' := by let := Classical.decEq ι; simp }
  map_update_add' u i x y :=
    ext fun _ => by let := Classical.decEq ι'; simp
  map_update_smul' u i c x :=
    ext fun _ => by let := Classical.de

Depends on / 依赖: Classical, Classical.decEq, Sum.rec, map_update_add, map_update_smul
-/
def currySum (f : MultilinearMap R N M₂) :
    MultilinearMap R (fun i : ι => N (.inl i)) (MultilinearMap R (fun i : ι' => N (.inr i)) M₂) where
  toFun u :=
    { toFun v := f (Sum.rec u v)
      map_update_add' := by let := Classical.decEq ι; simp
      map_update_smul' := by let := Classical.decEq ι; simp }
  map_update_add' u i x y :=
    ext fun _ => by let := Classical.decEq ι'; simp
  map_update_smul' u i c x :=
    ext fun _ => by let := Classical.decEq ι'; simp

@[simp low]
/--
theorem `currySum_apply` / 定理 `currySum_apply`

English:
theorem currySum_apply
  statement: (f : MultilinearMap R N M₂)
  proof: rfl

@[simp]

中文:
定理 currySum_apply
  结论: (f : MultilinearMap R N M₂)
  证明: rfl

@[simp]
-/
theorem currySum_apply (f : MultilinearMap R N M₂)
    (u : (i : ι) -> N (Sum.inl i)) (v : (i : ι') -> N (Sum.inr i)) :
    currySum f u v = f (Sum.rec u v) := rfl

@[simp]
/--
theorem `currySum_apply'` / 定理 `currySum_apply'`

English:
theorem currySum_apply'
  statement: {N : Type*} [AddCommMonoid N] [Module R N]
  proof: rfl

@[simp]

中文:
定理 currySum_apply'
  结论: {N : 类型} [AddCommMonoid N] [Module R N]
  证明: rfl

@[simp]
-/
theorem currySum_apply' {N : Type*} [AddCommMonoid N] [Module R N]
    (f : MultilinearMap R (fun _ : ι oplus ι' => N) M₂)
    (u : ι -> N) (v : ι' -> N) :
    currySum f u v = f (Sum.elim u v) := rfl

@[simp]
/--
lemma `currySum_add` / 引理 `currySum_add`

English:
lemma currySum_add
  given: (f₁ f₂ : MultilinearMap R N M₂)
  proof: rfl

@[simp]

中文:
引理 currySum_add
  条件: (f₁ f₂ : MultilinearMap R N M₂)
  证明: rfl

@[simp]
-/
lemma currySum_add (f₁ f₂ : MultilinearMap R N M₂) :
    currySum (f₁ + f₂) = currySum f₁ + currySum f₂ := rfl

@[simp]
/--
lemma `currySum_smul` / 引理 `currySum_smul`

English:
lemma currySum_smul
  given: (r : R) (f : MultilinearMap R N M₂)
  proof: rfl

中文:
引理 currySum_smul
  条件: (r : R) (f : MultilinearMap R N M₂)
  证明: rfl
-/
lemma currySum_smul (r : R) (f : MultilinearMap R N M₂) :
    currySum (r • f) = r • currySum f := rfl

/--
Definition of `uncurrySum` / `uncurrySum` 的定义

English:
definition uncurrySum
  body: g (fun i => u (.inl i)) (fun i' => u (.inr i'))
  map_update_add' := by
    let := Classical.decEq ι
    let := Classical.decEq ι'
    rintro _ _ (_ | _) _ _ <;> simp
  map_update_smul' := by
    let := Classical.decEq ι
    let := Classical.decEq ι'
    rintro _ _ (_ | _) _ _ <;> simp

@[simp]

中文:
定义 uncurrySum
  定义体: g (fun i => u (.inl i)) (fun i' => u (.inr i'))
  map_update_add' := by
    let := Classical.decEq ι
    let := Classical.decEq ι'
    rintro _ _ (_ | _) _ _ <;> simp
  map_update_smul' := by
    let := Classical.decEq ι
    let := Classical.decEq ι'
    rintro _ _ (_ | _) _ _ <;> simp

@[simp]
-/
def uncurrySum
    (g : MultilinearMap R (fun i : ι => N (.inl i))
      (MultilinearMap R (fun i : ι' => N (.inr i)) M₂)) :
    MultilinearMap R N M₂ where
  toFun u := g (fun i => u (.inl i)) (fun i' => u (.inr i'))
  map_update_add' := by
    let := Classical.decEq ι
    let := Classical.decEq ι'
    rintro _ _ (_ | _) _ _ <;> simp
  map_update_smul' := by
    let := Classical.decEq ι
    let := Classical.decEq ι'
    rintro _ _ (_ | _) _ _ <;> simp

@[simp]
/--
theorem `uncurrySum_apply` / 定理 `uncurrySum_apply`

English:
theorem uncurrySum_apply
  proof: rfl

@[simp]

中文:
定理 uncurrySum_apply
  证明: rfl

@[simp]
-/
theorem uncurrySum_apply
    (g : MultilinearMap R (fun i : ι => N (.inl i))
      (MultilinearMap R (fun i : ι' => N (.inr i)) M₂)) (u) :
    g.uncurrySum u =
      g (fun i => u (.inl i)) (fun i' => u (.inr i')) := rfl

@[simp]
/--
lemma `uncurrySum_add` / 引理 `uncurrySum_add`

English:
lemma uncurrySum_add
  proof: rfl

中文:
引理 uncurrySum_add
  证明: rfl
-/
lemma uncurrySum_add
    (g₁ g₂ : MultilinearMap R (fun i : ι => N (.inl i))
      (MultilinearMap R (fun i : ι' => N (.inr i)) M₂)) :
    uncurrySum (g₁ + g₂) = uncurrySum g₁ + uncurrySum g₂ :=
  rfl

/--
lemma `uncurrySum_smul` / 引理 `uncurrySum_smul`

English:
lemma uncurrySum_smul
  proof: rfl

@[simp]

中文:
引理 uncurrySum_smul
  证明: rfl

@[simp]
-/
lemma uncurrySum_smul
    (r : R) (g : MultilinearMap R (fun i : ι => N (.inl i))
      (MultilinearMap R (fun i : ι' => N (.inr i)) M₂)) :
    uncurrySum (r • g) = r • uncurrySum g :=
  rfl

@[simp]
/--
lemma `uncurrySum_currySum` / 引理 `uncurrySum_currySum`

English:
lemma uncurrySum_currySum
  given: (f : MultilinearMap R N M₂)
  proof: by
  ext
  simp only [uncurrySum_apply, currySum_apply]
  congr
  ext (_ | _) <;> simp

@[simp]

中文:
引理 uncurrySum_currySum
  条件: (f : MultilinearMap R N M₂)
  证明: by
  ext
  simp only [uncurrySum_apply, currySum_apply]
  congr
  ext (_ | _) <;> simp

@[simp]

Depends on / 依赖: currySum_apply, uncurrySum_apply
-/
lemma uncurrySum_currySum (f : MultilinearMap R N M₂) :
    uncurrySum (currySum f) = f := by
  ext
  simp only [uncurrySum_apply, currySum_apply]
  congr
  ext (_ | _) <;> simp

@[simp]
/--
lemma `currySum_uncurrySum` / 引理 `currySum_uncurrySum`

English:
lemma currySum_uncurrySum
  proof: rfl

中文:
引理 currySum_uncurrySum
  证明: rfl
-/
lemma currySum_uncurrySum
    (g : MultilinearMap R (fun i : ι => N (.inl i))
      (MultilinearMap R (fun i : ι' => N (.inr i)) M₂)) :
    currySum (uncurrySum g) = g :=
  rfl

/-- Multilinear maps on `N : (ι ⊕ ι') → Type*` identify to multilinear maps
from `(fun (i : ι) ↦ N (.inl i))` taking values in the space of
linear maps on `(fun (i : ι') ↦ N (.inr i))`. -/
@[simps]
/--
Definition of `currySumEquiv` / `currySumEquiv` 的定义

English:
definition currySumEquiv
  signature: : MultilinearMap R N M₂ ≃ₗ[R]
  body: currySum
  invFun := uncurrySum
  left_inv _ := by simp
  map_add' := by aesop
  map_smul' := by aesop

@[simp]

中文:
定义 currySumEquiv
  签名: : MultilinearMap R N M₂ ≃ₗ[R]
  定义体: currySum
  invFun := uncurrySum
  left_inv _ := by simp
  map_add' := by aesop
  map_smul' := by aesop

@[simp]

Depends on / 依赖: currySum
-/
def currySumEquiv : MultilinearMap R N M₂ ≃ₗ[R]
    MultilinearMap R (fun i : ι => N (.inl i))
      (MultilinearMap R (fun i : ι' => N (.inr i)) M₂) where
  toFun := currySum
  invFun := uncurrySum
  left_inv _ := by simp
  map_add' := by aesop
  map_smul' := by aesop

@[simp]
/--
theorem `coe_currySumEquiv` / 定理 `coe_currySumEquiv`

English:
theorem coe_currySumEquiv
  statement: ⇑(currySumEquiv (R := R) (N := N) (M₂ := M₂)) = currySum
  proof: rfl

@[simp]

中文:
定理 coe_currySumEquiv
  结论: ⇑(currySumEquiv (R := R) (N := N) (M₂ := M₂)) = currySum
  证明: rfl

@[simp]

Depends on / 依赖: currySum
-/
theorem coe_currySumEquiv : ⇑(currySumEquiv (R := R) (N := N) (M₂ := M₂)) = currySum :=
  rfl

@[simp]
/--
theorem `coe_currySumEquiv_symm` / 定理 `coe_currySumEquiv_symm`

English:
theorem coe_currySumEquiv_symm
  statement: ⇑(currySumEquiv (R := R) (N := N) (M₂ := M₂)).symm = uncurrySum
  proof: rfl

中文:
定理 coe_currySumEquiv_symm
  结论: ⇑(currySumEquiv (R := R) (N := N) (M₂ := M₂)).symm = uncurrySum
  证明: rfl

Depends on / 依赖: uncurrySum
-/
theorem coe_currySumEquiv_symm : ⇑(currySumEquiv (R := R) (N := N) (M₂ := M₂)).symm = uncurrySum :=
  rfl

variable (R M₂ M')

/--
Definition of `curryFinFinset` / `curryFinFinset` 的定义

English:
definition curryFinFinset
  signature: {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l)
  body: (domDomCongrLinearEquiv R R M' M₂ (finSumEquivOfFinset hk hl).symm).trans
    currySumEquiv

中文:
定义 curryFinFinset
  签名: {k l n : 自然数} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l)
  定义体: (domDomCongrLinearEquiv R R M' M₂ (finSumEquivOfFinset hk hl).symm).trans
    currySumEquiv

Depends on / 依赖: currySumEquiv, domDomCongrLinearEquiv, finSumEquivOfFinset
-/
def curryFinFinset {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l) :
    MultilinearMap R (fun _ : Fin n => M') M₂ ≃ₗ[R]
      MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂) :=
  (domDomCongrLinearEquiv R R M' M₂ (finSumEquivOfFinset hk hl).symm).trans
    currySumEquiv

variable {R M₂ M'}

@[simp]
/--
theorem `curryFinFinset_apply` / 定理 `curryFinFinset_apply`

English:
theorem curryFinFinset_apply
  statement: {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l)
  proof: rfl

@[simp]

中文:
定理 curryFinFinset_apply
  结论: {k l n : 自然数} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l)
  证明: rfl

@[simp]
-/
theorem curryFinFinset_apply {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin n => M') M₂) (mk : Fin k -> M') (ml : Fin l -> M') :
    curryFinFinset R M₂ M' hk hl f mk ml =
      f fun i => Sum.elim mk ml ((finSumEquivOfFinset hk hl).symm i) :=
  rfl

@[simp]
/--
theorem `curryFinFinset_symm_apply` / 定理 `curryFinFinset_symm_apply`

English:
theorem curryFinFinset_symm_apply
  statement: {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k)
  proof: rfl

中文:
定理 curryFinFinset_symm_apply
  结论: {k l n : 自然数} {s : Finset (Fin n)} (hk : #s = k)
  证明: rfl
-/
theorem curryFinFinset_symm_apply {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (m : Fin n -> M') :
    (curryFinFinset R M₂ M' hk hl).symm f m =
      f (fun i => m <| finSumEquivOfFinset hk hl (Sum.inl i)) fun i =>
m finSumEquivOfFinset hk hl (Sum.inr i) :=
  rfl

/--
theorem `curryFinFinset_symm_apply_piecewise_const` / 定理 `curryFinFinset_symm_apply_piecewise_const`

English:
theorem curryFinFinset_symm_apply_piecewise_const
  statement: {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k)
  proof: by
  rw [curryFinFinset_symm_apply]; congr
  · ext
    rw [finSumEquivOfFinset_inl]; rw [Finset.piecewise_eq_of_mem]
    apply Finset.orderEmbOfFin_mem
  · ext
    rw [finSumEquivOfFinset_inr]; rw [Finset.piecewise_eq_of_notMem]
    exact Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ _ _)

@[simp]

中文:
定理 curryFinFinset_symm_apply_piecewise_const
  结论: {k l n : 自然数} {s : Finset (Fin n)} (hk : #s = k)
  证明: by
  rw [curryFinFinset_symm_apply]; congr
  · ext
    rw [finSumEquivOfFinset_inl]; rw [Finset.piecewise_eq_of_mem]
    apply Finset.orderEmbOfFin_mem
  · ext
    rw [finSumEquivOfFinset_inr]; rw [Finset.piecewise_eq_of_notMem]
    exact Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ _ _)

@[simp]

Depends on / 依赖: Finset, Finset.mem_compl, Finset.orderEmbOfFin_mem, Finset.piecewise_eq_of_mem, Finset.piecewise_eq_of_notMem, curryFinFinset_symm_apply, finSumEquivOfFinset_inl, finSumEquivOfFinset_inr, mem_compl, orderEmbOfFin_mem, piecewise_eq_of_mem, piecewise_eq_of_notMem
-/
theorem curryFinFinset_symm_apply_piecewise_const {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (x y : M') :
    (curryFinFinset R M₂ M' hk hl).symm f (s.piecewise (fun _ => x) fun _ => y) =
      f (fun _ => x) fun _ => y := by
  rw [curryFinFinset_symm_apply]; congr
  · ext
    rw [finSumEquivOfFinset_inl]; rw [Finset.piecewise_eq_of_mem]
    apply Finset.orderEmbOfFin_mem
  · ext
    rw [finSumEquivOfFinset_inr]; rw [Finset.piecewise_eq_of_notMem]
    exact Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ _ _)

@[simp]
/--
theorem `curryFinFinset_symm_apply_const` / 定理 `curryFinFinset_symm_apply_const`

English:
theorem curryFinFinset_symm_apply_const
  statement: {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k)
  proof: rfl

中文:
定理 curryFinFinset_symm_apply_const
  结论: {k l n : 自然数} {s : Finset (Fin n)} (hk : #s = k)
  证明: rfl
-/
theorem curryFinFinset_symm_apply_const {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (x : M') : ((curryFinFinset R M₂ M' hk hl).symm f fun _ => x) = f (fun _ => x) fun _ => x :=
  rfl

/--
theorem `curryFinFinset_apply_const` / 定理 `curryFinFinset_apply_const`

English:
theorem curryFinFinset_apply_const
  statement: {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k)
  proof: by
  rw [← curryFinFinset_symm_apply_piecewise_const hk hl]; rw [LinearEquiv.symm_apply_apply]

中文:
定理 curryFinFinset_apply_const
  结论: {k l n : 自然数} {s : Finset (Fin n)} (hk : #s = k)
  证明: by
  rw [← curryFinFinset_symm_apply_piecewise_const hk hl]; rw [LinearEquiv.symm_apply_apply]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_apply, curryFinFinset_symm_apply_piecewise_const, symm_apply_apply
-/
theorem curryFinFinset_apply_const {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l) (f : MultilinearMap R (fun _ : Fin n => M') M₂) (x y : M') :
    (curryFinFinset R M₂ M' hk hl f (fun _ => x) fun _ => y) =
      f (s.piecewise (fun _ => x) fun _ => y) := by
  rw [← curryFinFinset_symm_apply_piecewise_const hk hl]; rw [LinearEquiv.symm_apply_apply]

end MultilinearMap
