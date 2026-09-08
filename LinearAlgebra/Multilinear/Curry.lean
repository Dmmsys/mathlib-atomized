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

variable {R : Type uR} {S : Type uS} {ι : Type uι} {ι' : Type uι'} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

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

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

/-! #### Left currying -/


/-- Given a linear map `f` from `M 0` to multilinear maps on `n` variables,
construct the corresponding multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (m 0) (tail m)` -/
/-
**LinearMap.uncurryLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.uncurryLeft (f : M 0 ->ₗ[R] MultilinearMap R (fun i : Fin n => M
 i.succ) M₂) : MultilinearMap R M M₂
参数：f : M 0 ->ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
Given a linear map `f` from `M 0` to multilinear maps on `n` variables,
construct the corresponding multilinear map on `n+1` variables obtained by conca
tenating
the variables, given by `m ↦ f (m 0) (tail m)`
-/
def LinearMap.uncurryLeft (f : M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂) :
    MultilinearMap R M M₂ :=
  MultilinearMap.mk' (fun m ↦ f (m 0) (tail m))
    (fun m i x y ↦ by cases i using Fin.cases <;> simp [Ne.symm])
    (fun m i c x ↦ by cases i using Fin.cases <;> simp [Ne.symm])

@[simp]
/-
**LinearMap.uncurryLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.uncurryLeft_apply (f : M 0 ->ₗ[R] MultilinearMap R (fun i : Fin 
n => M i.succ) M₂) (m : forall i, M i) : f.uncurryLeft m = f (m 0) (tail m)
参数：f : M 0 ->ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂；m : forall i, 
M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem LinearMap.uncurryLeft_apply (f : M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂)
    (m : ∀ i, M i) : f.uncurryLeft m = f (m 0) (tail m) :=
  rfl

/-- Given a multilinear map `f` in `n+1` variables, split the first variable to obtain
a linear map into multilinear maps in `n` variables, given by `x ↦ (m ↦ f (cons x m))`. -/
/-
**MultilinearMap.curryLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MultilinearMap.curryLeft (f : MultilinearMap R M M₂) : M 0 ->ₗ[R] Multilin
earMap R (fun i : Fin n => M i.succ) M₂ where toFun x
参数：f : MultilinearMap R M M₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
Given a multilinear map `f` in `n+1` variables, split the first variable to obta
in
a linear map into multilinear maps in `n` variables, given by `x ↦ (m ↦ f (cons 
x m))`.
-/
def MultilinearMap.curryLeft (f : MultilinearMap R M M₂) :
    M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂ where
  toFun x := MultilinearMap.mk' fun m => f (cons x m)
  map_add' x y := by
    ext m
    exact cons_add f m x y
  map_smul' c x := by
    ext m
    exact cons_smul f m c x

@[simp]
/-
**MultilinearMap.curryLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultilinearMap.curryLeft_apply (f : MultilinearMap R M M₂) (x : M 0) (m : 
forall i : Fin n, M i.succ) : f.curryLeft x m = f (cons x m)
参数：f : MultilinearMap R M M₂；x : M 0；m : forall i : Fin n, M i.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem MultilinearMap.curryLeft_apply (f : MultilinearMap R M M₂) (x : M 0)
    (m : ∀ i : Fin n, M i.succ) : f.curryLeft x m = f (cons x m) :=
  rfl

@[simp]
/-
**LinearMap.curry_uncurryLeft** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.curry_uncurryLeft (f : M 0 ->ₗ[R] MultilinearMap R (fun i : Fin 
n => M i.succ) M₂) : f.uncurryLeft.curryLeft = f
参数：f : M 0 ->ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem LinearMap.curry_uncurryLeft (f : M 0 →ₗ[R] MultilinearMap R (fun i :
    Fin n => M i.succ) M₂) : f.uncurryLeft.curryLeft = f := by
  rfl

@[simp]
/-
**MultilinearMap.uncurry_curryLeft** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultilinearMap.uncurry_curryLeft (f : MultilinearMap R M M₂) : f.curryLeft
.uncurryLeft = f
参数：f : MultilinearMap R M M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.cons_self_tail`：cons_self_tail : cons (q 0) (tail q) = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**multilinearCurryLeftEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：multilinearCurryLeftEquiv : MultilinearMap R M M₂ ≃ₗ[R] (M 0 ->ₗ[R] Multil
inearMap R (fun i : Fin n => M i.succ) M₂) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MultilinearMap.uncurry_curryLeft`：MultilinearMap.uncurry_curryLeft (f : 
MultilinearMap R M M₂) : f.curryLeft.uncurryLeft = f
· 使用定理 `LinearMap.curry_uncurryLeft`：LinearMap.curry_uncurryLeft (f : M 0 ->ₗ[R]
 MultilinearMap R (fun i : Fin n => M i.succ) M₂) : f.uncurryLeft.curryLeft = f

--- 原说明 ---
The space of multilinear maps on `Π (i : Fin (n+1)), M i` is canonically isomorp
hic to
the space of linear maps from `M 0` to the space of multilinear maps on
`Π (i : Fin n), M i.succ`, by separating the first variable. We register this is
omorphism as a
linear isomorphism in `multilinearCurryLeftEquiv R M M₂`.

The direct and inverse maps are given by `f.curryLeft` and `f.uncurryLeft`. Use 
these
unless you need the full framework of linear equivs.
-/
def multilinearCurryLeftEquiv :
    MultilinearMap R M M₂ ≃ₗ[R] (M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂) where
  toFun := MultilinearMap.curryLeft
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := LinearMap.uncurryLeft
  left_inv := MultilinearMap.uncurry_curryLeft
  right_inv := LinearMap.curry_uncurryLeft

variable {R M M₂}

/-! #### Right currying -/

/-- Given a multilinear map `f` in `n` variables to the space of linear maps from `M (last n)` to
`M₂`, construct the corresponding multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (init m) (m (last n))` -/
/-
**MultilinearMap.uncurryRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MultilinearMap.uncurryRight (f : MultilinearMap R (fun i : Fin n => M (cas
tSucc i)) (M (last n) ->ₗ[R] M₂)) : MultilinearMap R M M₂
参数：f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) ->ₗ[R] M₂)
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a multilinear map `f` in `n` variables to the space of linear maps from `M
 (last n)` to
`M₂`, construct the corresponding multilinear map on `n+1` variables obtained by
 concatenating
the variables, given by `m ↦ f (init m) (m (last n))`
-/
def MultilinearMap.uncurryRight
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂)) :
    MultilinearMap R M M₂ :=
  MultilinearMap.mk' (fun m ↦ f (init m) (m (last n)))
    (fun m i x y ↦ by cases i using Fin.lastCases <;> simp [Ne.symm])
    (fun m i c x ↦ by cases i using Fin.lastCases <;> simp [Ne.symm])

@[simp]
/-
**MultilinearMap.uncurryRight_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultilinearMap.uncurryRight_apply (f : MultilinearMap R (fun i : Fin n => 
M (castSucc i)) (M (last n) ->ₗ[R] M₂)) (m : forall i, M i) : f.uncurryRight m =
 f (init m) (m (last n))
参数：f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) ->ₗ[R] M₂)
；m : forall i, M i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MultilinearMap.uncurryRight_apply
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂))
    (m : ∀ i, M i) : f.uncurryRight m = f (init m) (m (last n)) :=
  rfl

/-- Given a multilinear map `f` in `n+1` variables, split the last variable to obtain
a multilinear map in `n` variables taking values in linear maps from `M (last n)` to `M₂`, given by
`m ↦ (x ↦ f (snoc m x))`. -/
/-
**MultilinearMap.curryRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MultilinearMap.curryRight (f : MultilinearMap R M M₂) : MultilinearMap R (
fun i : Fin n => M (Fin.castSucc i)) (M (last n) ->ₗ[R] M₂)
参数：f : MultilinearMap R M M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a multilinear map `f` in `n+1` variables, split the last variable to obtai
n
a multilinear map in `n` variables taking values in linear maps from `M (last n)
` to `M₂`, given by
`m ↦ (x ↦ f (snoc m x))`.
-/
def MultilinearMap.curryRight (f : MultilinearMap R M M₂) :
    MultilinearMap R (fun i : Fin n => M (Fin.castSucc i)) (M (last n) →ₗ[R] M₂) :=
  MultilinearMap.mk' fun m ↦
    { toFun := fun x => f (snoc m x)
      map_add' := fun x y => by simp_rw [f.snoc_add]
      map_smul' := fun c x => by simp only [f.snoc_smul, RingHom.id_apply] }

@[simp]
/-
**MultilinearMap.curryRight_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultilinearMap.curryRight_apply (f : MultilinearMap R M M₂) (m : forall i 
: Fin n, M (castSucc i)) (x : M (last n)) : f.curryRight m x = f (snoc m x)
参数：f : MultilinearMap R M M₂；m : forall i : Fin n, M (castSucc i)；x : M (last n)
。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MultilinearMap.curryRight_apply (f : MultilinearMap R M M₂)
    (m : ∀ i : Fin n, M (castSucc i)) (x : M (last n)) : f.curryRight m x = f (snoc m x) :=
  rfl

@[simp]
/-
**MultilinearMap.curry_uncurryRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultilinearMap.curry_uncurryRight (f : MultilinearMap R (fun i : Fin n => 
M (castSucc i)) (M (last n) ->ₗ[R] M₂)) : f.uncurryRight.curryRight = f
参数：f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) ->ₗ[R] M₂)
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `Fin.init_snoc`：init_snoc : init (snoc p x) = p
-/
theorem MultilinearMap.curry_uncurryRight
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂)) :
    f.uncurryRight.curryRight = f := by
  ext m x
  simp only [snoc_last, MultilinearMap.curryRight_apply, MultilinearMap.uncurryRight_apply]
  rw [init_snoc]

@[simp]
/-
**MultilinearMap.uncurry_curryRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultilinearMap.uncurry_curryRight (f : MultilinearMap R M M₂) : f.curryRig
ht.uncurryRight = f
参数：f : MultilinearMap R M M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.snoc_init_self`：snoc_init_self : snoc (init q) (q (last n)) = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem MultilinearMap.uncurry_curryRight (f : MultilinearMap R M M₂) :
    f.curryRight.uncurryRight = f := by
  ext m
  simp

variable (R M M₂)

/-- The space of multilinear maps on `Π (i : Fin (n+1)), M i` is canonically isomorphic to
the space of linear maps from the space of multilinear maps on `Π (i : Fin n), M (castSucc i)` to
the space of linear maps on `M (last n)`, by separating the last variable. We register this
isomorphism as a linear isomorphism in `multilinearCurryRightEquiv R M M₂`.

The direct and inverse maps are given by `f.curryRight` and `f.uncurryRight`. Use these
unless you need the full framework of linear equivs. -/
/-
**multilinearCurryRightEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：multilinearCurryRightEquiv : MultilinearMap R M M₂ ≃ₗ[R] MultilinearMap R 
(fun i : Fin n => M (castSucc i)) (M (last n) ->ₗ[R] M₂) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.uncurry_curryRight`：MultilinearMap.uncurry_curryRight (f 
: MultilinearMap R M M₂) : f.curryRight.uncurryRight = f
· 使用定理 `MultilinearMap.curry_uncurryRight`：MultilinearMap.curry_uncurryRight (f 
: MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) ->ₗ[R] M₂)) : f
.uncurryRight.curryRigh…

--- 原说明 ---
The space of multilinear maps on `Π (i : Fin (n+1)), M i` is canonically isomorp
hic to
the space of linear maps from the space of multilinear maps on `Π (i : Fin n), M
 (castSucc i)` to
the space of linear maps on `M (last n)`, by separating the last variable. We re
gister this
isomorphism as a linear isomorphism in `multilinearCurryRightEquiv R M M₂`.

The direct and inverse maps are given by `f.curryRight` and `f.uncurryRight`. Us
e these
unless you need the full framework of linear equivs.
-/
def multilinearCurryRightEquiv :
    MultilinearMap R M M₂ ≃ₗ[R]
      MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂) where
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
/-
**LinearMap.uncurryMid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.uncurryMid (p : Fin (n + 1)) (f : M p ->ₗ[R] MultilinearMap R (f
un i => M (p.succAbove i)) M₂) : MultilinearMap R M M₂
参数：p : Fin (n + 1)；f : M p ->ₗ[R] MultilinearMap R (fun i => M (p.succAbove i)) 
M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a linear map from `M p` to the space of multilinear maps
in `n` variables `M 0`, ..., `M n` with `M p` removed,
returns a multilinear map in all `n + 1` variables.
-/
def LinearMap.uncurryMid (p : Fin (n + 1))
    (f : M p →ₗ[R] MultilinearMap R (fun i ↦ M (p.succAbove i)) M₂) : MultilinearMap R M M₂ :=
  .mk' (fun m ↦ f (m p) (p.removeNth m))
    (fun m i x y ↦ by cases i using Fin.succAboveCases p <;> simp)
    (fun m i x y ↦ by cases i using Fin.succAboveCases p <;> simp)

/-- Interpret a multilinear map in `n + 1` variables
as a linear map in `p`th variable with values in the multilinear maps in the other variables. -/
@[simps!]
/-
**MultilinearMap.curryMid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MultilinearMap.curryMid (p : Fin (n + 1)) (f : MultilinearMap R M M₂) : M 
p ->ₗ[R] MultilinearMap R (fun i => M (p.succAbove i)) M₂ where toFun x
参数：p : Fin (n + 1)；f : MultilinearMap R M M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a multilinear map in `n + 1` variables
as a linear map in `p`th variable with values in the multilinear maps in the oth
er variables.
-/
def MultilinearMap.curryMid (p : Fin (n + 1)) (f : MultilinearMap R M M₂) :
    M p →ₗ[R] MultilinearMap R (fun i ↦ M (p.succAbove i)) M₂ where
  toFun x := .mk' fun m ↦ f (p.insertNth x m)
  map_add' x y := by ext; simp [map_insertNth_add]
  map_smul' c x := by ext; simp [map_insertNth_smul]

@[simp]
/-
**LinearMap.curryMid_uncurryMid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.curryMid_uncurryMid (i : Fin (n + 1)) (f : M i ->ₗ[R] Multilinea
rMap R (fun j => M (i.succAbove j)) M₂) : (f.uncurryMid i).curryMid i = f
参数：i : Fin (n + 1)；f : M i ->ₗ[R] MultilinearMap R (fun j => M (i.succAbove j)) 
M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.curryMid_apply_apply`：∀ {R : Type uR} {n : ℕ} {M : Fin n.
succ → Type v} {M₂ : Type v₂} [inst : CommSemiring R]   [inst_1 : (i : Fin n.suc
c) → AddCommMonoid (M i)]…
· 使用定理 `LinearMap.uncurryMid_apply`：∀ {R : Type uR} {n : ℕ} {M : Fin n.succ → Ty
pe v} {M₂ : Type v₂} [inst : CommSemiring R]   [inst_1 : (i : Fin n.succ) → AddC
ommMonoid (M i)]…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `Fin.removeNth_insertNth`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin
 (n + 1)) (a : α p) (f : (i : Fin n) → α (p.succAbove i)),   p.removeNth (p.inse
rtNth a f) = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.curryMid_uncurryMid (i : Fin (n + 1))
    (f : M i →ₗ[R] MultilinearMap R (fun j ↦ M (i.succAbove j)) M₂) :
    (f.uncurryMid i).curryMid i = f := by ext; simp

@[simp]
/-
**MultilinearMap.uncurryMid_curryMid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultilinearMap.uncurryMid_curryMid (i : Fin (n + 1)) (f : MultilinearMap R
 M M₂) : (f.curryMid i).uncurryMid i = f
参数：i : Fin (n + 1)；f : MultilinearMap R M M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.uncurryMid_apply`：∀ {R : Type uR} {n : ℕ} {M : Fin n.succ → Ty
pe v} {M₂ : Type v₂} [inst : CommSemiring R]   [inst_1 : (i : Fin n.succ) → AddC
ommMonoid (M i)]…
· 使用定理 `MultilinearMap.curryMid_apply_apply`：∀ {R : Type uR} {n : ℕ} {M : Fin n.
succ → Type v} {M₂ : Type v₂} [inst : CommSemiring R]   [inst_1 : (i : Fin n.suc
c) → AddCommMonoid (M i)]…
· 使用定理 `Fin.insertNth_removeNth`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin
 (n + 1)) (x : α p) (f : (j : Fin (n + 1)) → α j),   p.insertNth x (p.removeNth 
f) = Function…
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem MultilinearMap.uncurryMid_curryMid (i : Fin (n + 1)) (f : MultilinearMap R M M₂) :
    (f.curryMid i).uncurryMid i = f := by ext; simp

variable (R M M₂)

/-- `MultilinearMap.curryMid` as a linear equivalence. -/
@[simps]
/-
**MultilinearMap.curryMidLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MultilinearMap.curryMidLinearEquiv (p : Fin (n + 1)) : MultilinearMap R M 
M₂ ≃ₗ[R] M p ->ₗ[R] MultilinearMap R (fun i => M (p.succAbove i)) M₂ where toFun
参数：p : Fin (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.uncurryMid_curryMid`：MultilinearMap.uncurryMid_curryMid (
i : Fin (n + 1)) (f : MultilinearMap R M M₂) : (f.curryMid i).uncurryMid i = f
· 使用定理 `LinearMap.curryMid_uncurryMid`：LinearMap.curryMid_uncurryMid (i : Fin (n
 + 1)) (f : M i ->ₗ[R] MultilinearMap R (fun j => M (i.succAbove j)) M₂) : (f.un
curryMid i).curryMi…

--- 原说明 ---
`MultilinearMap.curryMid` as a linear equivalence.
-/
def MultilinearMap.curryMidLinearEquiv (p : Fin (n + 1)) :
    MultilinearMap R M M₂ ≃ₗ[R] M p →ₗ[R] MultilinearMap R (fun i ↦ M (p.succAbove i)) M₂ where
  toFun := MultilinearMap.curryMid p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := LinearMap.uncurryMid p
  left_inv := MultilinearMap.uncurryMid_curryMid p
  right_inv := LinearMap.curryMid_uncurryMid p

namespace MultilinearMap

variable {R M₂} {N : (ι ⊕ ι') → Type*}
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- Given a family of modules `N : (ι ⊕ ι') → Type*`, a multilinear map
on `(fun _ : ι ⊕ ι' => M')` induces a multilinear map on
`(fun (i : ι) ↦ N (.inl i))` taking values in the space of
linear maps on `(fun (i : ι') ↦ N (.inr i))`. -/
/-
**MultilinearMap.currySum** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：currySum (f : MultilinearMap R N M₂) : MultilinearMap R (fun i : ι => N (.
inl i)) (MultilinearMap R (fun i : ι' => N (.inr i)) M₂) where toFun u
参数：f : MultilinearMap R N M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of modules `N : (ι ⊕ ι') → Type*`, a multilinear map
on `(fun _ : ι ⊕ ι' => M')` induces a multilinear map on
`(fun (i : ι) ↦ N (.inl i))` taking values in the space of
linear maps on `(fun (i : ι') ↦ N (.inr i))`.
-/
def currySum (f : MultilinearMap R N M₂) :
    MultilinearMap R (fun i : ι ↦ N (.inl i)) (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂) where
  toFun u :=
    { toFun v := f (Sum.rec u v)
      map_update_add' := by let := Classical.decEq ι; simp
      map_update_smul' := by let := Classical.decEq ι; simp }
  map_update_add' u i x y :=
    ext fun _ ↦ by let := Classical.decEq ι'; simp
  map_update_smul' u i c x :=
    ext fun _ ↦ by let := Classical.decEq ι'; simp

@[simp low]
/-
**MultilinearMap.currySum_apply** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：currySum_apply (f : MultilinearMap R N M₂) (u : (i : ι) -> N (Sum.inl i)) 
(v : (i : ι') -> N (Sum.inr i)) : currySum f u v = f (Sum.rec u v)
参数：f : MultilinearMap R N M₂；u : (i : ι) -> N (Sum.inl i)；v : (i : ι') -> N (Sum
.inr i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem currySum_apply (f : MultilinearMap R N M₂)
    (u : (i : ι) → N (Sum.inl i)) (v : (i : ι') → N (Sum.inr i)) :
    currySum f u v = f (Sum.rec u v) := rfl

@[simp]
/-
**MultilinearMap.currySum_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：currySum_apply' {N : Type*} [AddCommMonoid N] [Module R N] (f : Multilinea
rMap R (fun _ : ι oplus ι' => N) M₂) (u : ι -> N) (v : ι' -> N) : currySum f u v
 = f (Sum.elim u v)
参数：f : MultilinearMap R (fun _ : ι oplus ι' => N) M₂；u : ι -> N；v : ι' -> N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem currySum_apply' {N : Type*} [AddCommMonoid N] [Module R N]
    (f : MultilinearMap R (fun _ : ι ⊕ ι' ↦ N) M₂)
    (u : ι → N) (v : ι' → N) :
    currySum f u v = f (Sum.elim u v) := rfl

@[simp]
/-
**MultilinearMap.currySum_add** 是 Mathlib 中的一个引理，位于命名空间 `MultilinearMap`。
形式化陈述：currySum_add (f₁ f₂ : MultilinearMap R N M₂) : currySum (f₁ + f₂) = curryS
um f₁ + currySum f₂
参数：f₁ f₂ : MultilinearMap R N M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma currySum_add (f₁ f₂ : MultilinearMap R N M₂) :
    currySum (f₁ + f₂) = currySum f₁ + currySum f₂ := rfl

@[simp]
/-
**MultilinearMap.currySum_smul** 是 Mathlib 中的一个引理，位于命名空间 `MultilinearMap`。
形式化陈述：currySum_smul (r : R) (f : MultilinearMap R N M₂) : currySum (r • f) = r •
 currySum f
参数：r : R；f : MultilinearMap R N M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma currySum_smul (r : R) (f : MultilinearMap R N M₂) :
    currySum (r • f) = r • currySum f := rfl

/-- Given a family of modules `N : (ι ⊕ ι') → Type*`, a multilinear map on
`(fun (i : ι) ↦ N (.inl i))` taking values in the space of
linear maps on `(fun (i : ι') ↦ N (.inr i))` induces a multilinear map
on `(fun _ : ι ⊕ ι' => M')` induces. -/
/-
**MultilinearMap.uncurrySum** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：uncurrySum (g : MultilinearMap R (fun i : ι => N (.inl i)) (MultilinearMap
 R (fun i : ι' => N (.inr i)) M₂)) : MultilinearMap R N M₂ where toFun u
参数：g : MultilinearMap R (fun i : ι => N (.inl i)) (MultilinearMap R (fun i : ι' 
=> N (.inr i)) M₂)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of modules `N : (ι ⊕ ι') → Type*`, a multilinear map on
`(fun (i : ι) ↦ N (.inl i))` taking values in the space of
linear maps on `(fun (i : ι') ↦ N (.inr i))` induces a multilinear map
on `(fun _ : ι ⊕ ι' => M')` induces.
-/
def uncurrySum
    (g : MultilinearMap R (fun i : ι ↦ N (.inl i))
      (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂)) :
    MultilinearMap R N M₂ where
  toFun u := g (fun i ↦ u (.inl i)) (fun i' ↦ u (.inr i'))
  map_update_add' := by
    let := Classical.decEq ι
    let := Classical.decEq ι'
    rintro _ _ (_ | _) _ _ <;> simp
  map_update_smul' := by
    let := Classical.decEq ι
    let := Classical.decEq ι'
    rintro _ _ (_ | _) _ _ <;> simp

@[simp]
/-
**MultilinearMap.uncurrySum_apply** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：uncurrySum_apply (g : MultilinearMap R (fun i : ι => N (.inl i)) (Multilin
earMap R (fun i : ι' => N (.inr i)) M₂)) (u) : g.uncurrySum u = g (fun i => u (.
inl i)) (fun i' => u (.inr i'))
参数：g : MultilinearMap R (fun i : ι => N (.inl i)) (MultilinearMap R (fun i : ι' 
=> N (.inr i)) M₂)；u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uncurrySum_apply
    (g : MultilinearMap R (fun i : ι ↦ N (.inl i))
      (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂)) (u) :
    g.uncurrySum u =
      g (fun i ↦ u (.inl i)) (fun i' ↦ u (.inr i')) := rfl

@[simp]
/-
**MultilinearMap.uncurrySum_add** 是 Mathlib 中的一个引理，位于命名空间 `MultilinearMap`。
形式化陈述：uncurrySum_add (g₁ g₂ : MultilinearMap R (fun i : ι => N (.inl i)) (Multil
inearMap R (fun i : ι' => N (.inr i)) M₂)) : uncurrySum (g₁ + g₂) = uncurrySum g
₁ + uncurrySum g₂
参数：g₁ g₂ : MultilinearMap R (fun i : ι => N (.inl i)) (MultilinearMap R (fun i :
 ι' => N (.inr i)) M₂)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uncurrySum_add
    (g₁ g₂ : MultilinearMap R (fun i : ι ↦ N (.inl i))
      (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂)) :
    uncurrySum (g₁ + g₂) = uncurrySum g₁ + uncurrySum g₂ :=
  rfl
/-
**MultilinearMap.uncurrySum_smul** 是 Mathlib 中的一个引理，位于命名空间 `MultilinearMap`。
形式化陈述：uncurrySum_smul (r : R) (g : MultilinearMap R (fun i : ι => N (.inl i)) (M
ultilinearMap R (fun i : ι' => N (.inr i)) M₂)) : uncurrySum (r • g) = r • uncur
rySum g
参数：r : R；g : MultilinearMap R (fun i : ι => N (.inl i)) (MultilinearMap R (fun i
 : ι' => N (.inr i)) M₂)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uncurrySum_smul
    (r : R) (g : MultilinearMap R (fun i : ι ↦ N (.inl i))
      (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂)) :
    uncurrySum (r • g) = r • uncurrySum g :=
  rfl

@[simp]
/-
**MultilinearMap.uncurrySum_currySum** 是 Mathlib 中的一个引理，位于命名空间 `MultilinearMap`。
形式化陈述：uncurrySum_currySum (f : MultilinearMap R N M₂) : uncurrySum (currySum f) 
= f
参数：f : MultilinearMap R N M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uncurrySum_currySum (f : MultilinearMap R N M₂) :
    uncurrySum (currySum f) = f := by
  ext
  simp only [uncurrySum_apply, currySum_apply]
  congr
  ext (_ | _) <;> simp

@[simp]
/-
**MultilinearMap.currySum_uncurrySum** 是 Mathlib 中的一个引理，位于命名空间 `MultilinearMap`。
形式化陈述：currySum_uncurrySum (g : MultilinearMap R (fun i : ι => N (.inl i)) (Multi
linearMap R (fun i : ι' => N (.inr i)) M₂)) : currySum (uncurrySum g) = g
参数：g : MultilinearMap R (fun i : ι => N (.inl i)) (MultilinearMap R (fun i : ι' 
=> N (.inr i)) M₂)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma currySum_uncurrySum
    (g : MultilinearMap R (fun i : ι ↦ N (.inl i))
      (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂)) :
    currySum (uncurrySum g) = g :=
  rfl

/-- Multilinear maps on `N : (ι ⊕ ι') → Type*` identify to multilinear maps
from `(fun (i : ι) ↦ N (.inl i))` taking values in the space of
linear maps on `(fun (i : ι') ↦ N (.inr i))`. -/
@[simps]
/-
**MultilinearMap.currySumEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：currySumEquiv : MultilinearMap R N M₂ ≃ₗ[R] MultilinearMap R (fun i : ι =>
 N (.inl i)) (MultilinearMap R (fun i : ι' => N (.inr i)) M₂) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multilinear maps on `N : (ι ⊕ ι') → Type*` identify to multilinear maps
from `(fun (i : ι) ↦ N (.inl i))` taking values in the space of
linear maps on `(fun (i : ι') ↦ N (.inr i))`.
-/
def currySumEquiv : MultilinearMap R N M₂ ≃ₗ[R]
    MultilinearMap R (fun i : ι ↦ N (.inl i))
      (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂) where
  toFun := currySum
  invFun := uncurrySum
  left_inv _ := by simp
  map_add' := by aesop
  map_smul' := by aesop

@[simp]
/-
**MultilinearMap.coe_currySumEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：coe_currySumEquiv : ⇑(currySumEquiv (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_currySumEquiv : ⇑(currySumEquiv (R := R) (N := N) (M₂ := M₂)) = currySum :=
  rfl

@[simp]
/-
**MultilinearMap.coe_currySumEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMa
p`。
形式化陈述：coe_currySumEquiv_symm : ⇑(currySumEquiv (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_currySumEquiv_symm : ⇑(currySumEquiv (R := R) (N := N) (M₂ := M₂)).symm = uncurrySum :=
  rfl

variable (R M₂ M')

/-- If `s : Finset (Fin n)` is a finite set of cardinality `k` and its complement has cardinality
`l`, then the space of multilinear maps on `fun i : Fin n => M'` is isomorphic to the space of
multilinear maps on `fun i : Fin k => M'` taking values in the space of multilinear maps
on `fun i : Fin l => M'`. -/
/-
**MultilinearMap.curryFinFinset** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：curryFinFinset {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ 
= l) : MultilinearMap R (fun _ : Fin n => M') M₂ ≃ₗ[R] MultilinearMap R (fun _ :
 Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂)
参数：Fin n；hk : #s = k；hl : #sᶜ = l。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `s : Finset (Fin n)` is a finite set of cardinality `k` and its complement ha
s cardinality
`l`, then the space of multilinear maps on `fun i : Fin n => M'` is isomorphic t
o the space of
multilinear maps on `fun i : Fin k => M'` taking values in the space of multilin
ear maps
on `fun i : Fin l => M'`.
-/
def curryFinFinset {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l) :
    MultilinearMap R (fun _ : Fin n => M') M₂ ≃ₗ[R]
      MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂) :=
  (domDomCongrLinearEquiv R R M' M₂ (finSumEquivOfFinset hk hl).symm).trans
    currySumEquiv

variable {R M₂ M'}

@[simp]
/-
**MultilinearMap.curryFinFinset_apply** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`
。
形式化陈述：curryFinFinset_apply {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k) (hl 
: #sᶜ = l) (f : MultilinearMap R (fun _ : Fin n => M') M₂) (mk : Fin k -> M') (m
l : Fin l -> M') : curryFinFinset R M₂ M' hk hl f mk ml = f fun i => Sum.elim mk
 ml ((finSumEquivOfFinset hk hl).symm i)
参数：Fin n；hk : #s = k；hl : #sᶜ = l；f : MultilinearMap R (fun _ : Fin n => M') M₂；
mk : Fin k -> M'；ml : Fin l -> M'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curryFinFinset_apply {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin n => M') M₂) (mk : Fin k → M') (ml : Fin l → M') :
    curryFinFinset R M₂ M' hk hl f mk ml =
      f fun i => Sum.elim mk ml ((finSumEquivOfFinset hk hl).symm i) :=
  rfl

@[simp]
/-
**MultilinearMap.curryFinFinset_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Multilinea
rMap`。
形式化陈述：curryFinFinset_symm_apply {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k)
 (hl : #sᶜ = l) (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (f
un _ : Fin l => M') M₂)) (m : Fin n -> M') : (curryFinFinset R M₂ M' hk hl).symm
 f m = f (fun i => m <| finSumEquivOfFinset hk hl (Sum.inl i)) fun i => m finSum
EquivOfFinset hk hl (Sum.inr i)
参数：Fin n；hk : #s = k；hl : #sᶜ = l；f : MultilinearMap R (fun _ : Fin k => M') (Mu
ltilinearMap R (fun _ : Fin l => M') M₂)；m : Fin n -> M'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curryFinFinset_symm_apply {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (m : Fin n → M') :
    (curryFinFinset R M₂ M' hk hl).symm f m =
      f (fun i => m <| finSumEquivOfFinset hk hl (Sum.inl i)) fun i =>
        m <| finSumEquivOfFinset hk hl (Sum.inr i) :=
  rfl
/-
**MultilinearMap.curryFinFinset_symm_apply_piecewise_const** 是 Mathlib 中的一个定理，位于
命名空间 `MultilinearMap`。
形式化陈述：curryFinFinset_symm_apply_piecewise_const {k l n : Nat} {s : Finset (Fin n
)} (hk : #s = k) (hl : #sᶜ = l) (f : MultilinearMap R (fun _ : Fin k => M') (Mul
tilinearMap R (fun _ : Fin l => M') M₂)) (x y : M') : (curryFinFinset R M₂ M' hk
 hl).symm f (s.piecewise (fun _ => x) fun _ => y) = f (fun _ => x) fun _ => y
参数：Fin n；hk : #s = k；hl : #sᶜ = l；f : MultilinearMap R (fun _ : Fin k => M') (Mu
ltilinearMap R (fun _ : Fin l => M') M₂)；x y : M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.curryFinFinset_symm_apply`：curryFinFinset_symm_apply {k l
 n : Nat} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l) (f : MultilinearMap 
R (fun _ : Fin k => M') (Multi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finSumEquivOfFinset_inl`：finSumEquivOfFinset_inl (hm : #s = m) (hn : #sᶜ
 = n) (i : Fin m) : finSumEquivOfFinset hm hn (Sum.inl i) = s.orderEmbOfFin hm i
· 使用引理 `Finset.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : ι} (hi : i in s) : 
s.piecewise f g i = f i
· 使用定理 `Finset.orderEmbOfFin_mem`：orderEmbOfFin_mem (s : Finset α) {k : Nat} (h 
: s.card = k) (i : Fin k) : s.orderEmbOfFin h i in s
· 使用定理 `finSumEquivOfFinset_inr`：finSumEquivOfFinset_inr (hm : #s = m) (hn : #sᶜ
 = n) (i : Fin n) : finSumEquivOfFinset hm hn (Sum.inr i) = sᶜ.orderEmbOfFin hn 
i
· 使用引理 `Finset.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : ι} (hi : i ∉ 
s) : s.piecewise f g i = g i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_compl`：mem_compl : a in sᶜ ↔ a ∉ s
-/
theorem curryFinFinset_symm_apply_piecewise_const {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (x y : M') :
    (curryFinFinset R M₂ M' hk hl).symm f (s.piecewise (fun _ => x) fun _ => y) =
      f (fun _ => x) fun _ => y := by
  rw [curryFinFinset_symm_apply]; congr
  · ext
    rw [finSumEquivOfFinset_inl, Finset.piecewise_eq_of_mem]
    apply Finset.orderEmbOfFin_mem
  · ext
    rw [finSumEquivOfFinset_inr, Finset.piecewise_eq_of_notMem]
    exact Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ _ _)

@[simp]
/-
**MultilinearMap.curryFinFinset_symm_apply_const** 是 Mathlib 中的一个定理，位于命名空间 `Mult
ilinearMap`。
形式化陈述：curryFinFinset_symm_apply_const {k l n : Nat} {s : Finset (Fin n)} (hk : #
s = k) (hl : #sᶜ = l) (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMa
p R (fun _ : Fin l => M') M₂)) (x : M') : ((curryFinFinset R M₂ M' hk hl).symm f
 fun _ => x) = f (fun _ => x) fun _ => x
参数：Fin n；hk : #s = k；hl : #sᶜ = l；f : MultilinearMap R (fun _ : Fin k => M') (Mu
ltilinearMap R (fun _ : Fin l => M') M₂)；x : M'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curryFinFinset_symm_apply_const {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (x : M') : ((curryFinFinset R M₂ M' hk hl).symm f fun _ => x) = f (fun _ => x) fun _ => x :=
  rfl
/-
**MultilinearMap.curryFinFinset_apply_const** 是 Mathlib 中的一个定理，位于命名空间 `Multiline
arMap`。
形式化陈述：curryFinFinset_apply_const {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k
) (hl : #sᶜ = l) (f : MultilinearMap R (fun _ : Fin n => M') M₂) (x y : M') : (c
urryFinFinset R M₂ M' hk hl f (fun _ => x) fun _ => y) = f (s.piecewise (fun _ =
> x) fun _ => y)
参数：Fin n；hk : #s = k；hl : #sᶜ = l；f : MultilinearMap R (fun _ : Fin n => M') M₂；
x y : M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MultilinearMap.curryFinFinset_symm_apply_piecewise_const`：curryFinFinset
_symm_apply_piecewise_const {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k) (hl
 : #sᶜ = l) (f : MultilinearMap R (fun _ : Fin…
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem curryFinFinset_apply_const {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l) (f : MultilinearMap R (fun _ : Fin n => M') M₂) (x y : M') :
    (curryFinFinset R M₂ M' hk hl f (fun _ => x) fun _ => y) =
      f (s.piecewise (fun _ => x) fun _ => y) := by
  rw [← curryFinFinset_symm_apply_piecewise_const hk hl, LinearEquiv.symm_apply_apply]

end MultilinearMap

