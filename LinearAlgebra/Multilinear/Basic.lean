/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.FunLike.Group
public import Mathlib.Data.FunLike.Module
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Order.BigOperators.Group.Finset


/-!
# Multilinear maps

We define multilinear maps as maps from `∀ (i : ι), M₁ i` to `M₂` which are linear in each
coordinate. Here, `M₁ i` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type
(although some statements will require it to be a fintype). This space, denoted by
`MultilinearMap R M₁ M₂`, inherits a module structure by pointwise addition and multiplication.

## Main definitions

* `MultilinearMap R M₁ M₂` is the space of multilinear maps from `∀ (i : ι), M₁ i` to `M₂`.
* `f.map_update_smul` is the multiplicativity of the multilinear map `f` along each coordinate.
* `f.map_update_add` is the additivity of the multilinear map `f` along each coordinate.
* `f.map_smul_univ` expresses the multiplicativity of `f` over all coordinates at the same time,
  writing `f (fun i => c i • m i)` as `(∏ i, c i) • f m`.
* `f.map_add_univ` expresses the additivity of `f` over all coordinates at the same time, writing

  `f (m + m')` as the sum over all subsets `s` of `ι` of `f (s.piecewise m m')`.
* `f.map_sum` expresses `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` as the sum of
  `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all possible functions.

See `Mathlib/LinearAlgebra/Multilinear/Curry.lean` for the currying of multilinear maps.

## Implementation notes

Expressing that a map is linear along the `i`-th coordinate when all other coordinates are fixed
can be done in two (equivalent) different ways:

* fixing a vector `m : ∀ (j : ι - i), M₁ j.val`, and then choosing separately the `i`-th coordinate
* fixing a vector `m : ∀ j, M₁ j`, and then modifying its `i`-th coordinate

The second way is more artificial as the value of `m` at `i` is not relevant, but it has the
advantage of avoiding subtype inclusion issues. This is the definition we use, based on
`Function.update` that allows to change the value of `m` at `i`.

Note that the use of `Function.update` requires a `DecidableEq ι` term to appear somewhere in the
statement of `MultilinearMap.map_update_add'` and `MultilinearMap.map_update_smul'`.
Three possible choices are:

1. Requiring `DecidableEq ι` as an argument to `MultilinearMap` (as we did originally).
2. Using `Classical.decEq ι` in the statement of `map_add'` and `map_smul'`.
3. Quantifying over all possible `DecidableEq ι` instances in the statement of `map_add'` and
   `map_smul'`.

Option 1 works fine, but puts unnecessary constraints on the user
(the zero map certainly does not need decidability).
Option 2 looks great at first, but in the common case when `ι = Fin n`
it introduces non-defeq decidability instance diamonds
within the context of proving `map_update_add'` and `map_update_smul'`,
of the form `Fin.decidableEq n = Classical.decEq (Fin n)`.
Option 3 of course does something similar, but of the form `Fin.decidableEq n = _inst`,
which is much easier to clean up since `_inst` is a free variable
and so the equality can just be substituted.
-/

@[expose] public section

open Fin Function Finset Set

universe uR uS uι v v' v₁ v₁' v₁'' v₂ v₃ v₄

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : Nat}
  {M : Fin n.succ -> Type v} {M₁ : ι -> Type v₁} {M₁' : ι -> Type v₁'} {M₁'' : ι -> Type v₁''}
variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

-- Don't generate injectivity lemmas, which the `simpNF` linter will time out on.
set_option genInjectivity false in
/--
Definition of `MultilinearMap` / `MultilinearMap` 的定义

English:
structure MultilinearMap
  parameters: (R : Type uR) {ι : Type uι} (M₁ : ι -> Type v₁) (M₂ : Type v₂) [Semiring R]
  axioms and operations (3):
    - toFun : (forall i, M₁ i) -> M₂
    - map_update_add' : forall [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x y : M₁ i), toFun (update m i (x + y)) = toFun (update m i x) + toFun (update m i y)
    - map_update_smul' : forall [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (c : R) (x : M₁ i), toFun (update m i (c • x)) = c • toFun (update m i x)

中文:
结构 多重线性映射
  参数: (R : 类型uR) {ι : 类型uι} (M₁ : ι -> 类型v₁) (M₂ : 类型v₂) [半环 R]
  公理与运算 (3 个):
    - toFun : (对任意 i, M₁ i) -> M₂
    - map_update_add' : 对任意 [DecidableEq ι] (m : 对任意 i, M₁ i) (i : ι) (x y : M₁ i), toFun (update m i (x + y)) = toFun (update m i x) + toFun (update m i y)
    - map_update_smul' : 对任意 [DecidableEq ι] (m : 对任意 i, M₁ i) (i : ι) (c : R) (x : M₁ i), toFun (update m i (c • x)) = c • toFun (update m i x)
-/
structure MultilinearMap (R : Type uR) {ι : Type uι} (M₁ : ι -> Type v₁) (M₂ : Type v₂) [Semiring R]
  [forall i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [forall i, Module R (M₁ i)] [Module R M₂] where
  /-- The underlying multivariate function of a multilinear map. -/
  toFun : (forall i, M₁ i) -> M₂
  /-- A multilinear map is additive in every argument. -/
  map_update_add' :
    forall [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x y : M₁ i),
      toFun (update m i (x + y)) = toFun (update m i x) + toFun (update m i y)
  /-- A multilinear map is compatible with scalar multiplication in every argument. -/
  map_update_smul' :
    forall [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (c : R) (x : M₁ i),
      toFun (update m i (c • x)) = c • toFun (update m i x)

namespace MultilinearMap

section Semiring

variable [Semiring R] [forall i, AddCommMonoid (M i)] [forall i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [AddCommMonoid M'] [forall i, Module R (M i)] [forall i, Module R (M₁ i)] [Module R M₂]
  [Module R M₃] [Module R M'] (f f' : MultilinearMap R M₁ M₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (MultilinearMap R M₁ M₂) (forall i, M₁ i) M₂
  body: f.toFun
  coe_injective f g h := by cases f; cases g; cases h; rfl

initialize_simps_projections MultilinearMap (toFun -> apply)

中文:
实例 :
  签名: 函数状 (多重线性映射 R M₁ M₂) (对任意 i, M₁ i) M₂
  定义体: f.toFun
  coe_injective f g h := by cases f; cases g; cases h; rfl

initialize_simps_projections MultilinearMap (toFun -> apply)

Depends on / 依赖: f.toFun
-/
instance : FunLike (MultilinearMap R M₁ M₂) (forall i, M₁ i) M₂ where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; cases h; rfl

initialize_simps_projections MultilinearMap (toFun -> apply)

/-- Constructor for `MultilinearMap R M₁ M₂` when the
index type `ι` is already endowed with a `DecidableEq` instance. -/
@[simps]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: [DecidableEq ι] (f : (forall i, M₁ i) -> M₂)
  body: f
  map_update_add' m i x y := by convert! h₁ m i x y
  map_update_smul' m i c x := by convert! h₂ m i c x

@[simp]

中文:
定义 mk'
  签名: [DecidableEq ι] (f : (对任意 i, M₁ i) -> M₂)
  定义体: f
  map_update_add' m i x y := by convert! h₁ m i x y
  map_update_smul' m i c x := by convert! h₂ m i c x

@[simp]

Depends on / 依赖: MultilinearMap, convert, map_update_add, map_update_smul, update
-/
def mk' [DecidableEq ι] (f : (forall i, M₁ i) -> M₂)
    (h₁ : forall (m : forall i, M₁ i) (i : ι) (x y : M₁ i),
      f (update m i (x + y)) = f (update m i x) + f (update m i y) := by aesop)
    (h₂ : forall (m : forall i, M₁ i) (i : ι) (c : R) (x : M₁ i),
      f (update m i (c • x)) = c • f (update m i x) := by aesop) :
    MultilinearMap R M₁ M₂ where
  toFun := f
  map_update_add' m i x y := by convert! h₁ m i x y
  map_update_smul' m i c x := by convert! h₂ m i c x

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  statement: f.toFun = ⇑f
  proof: rfl

@[simp]

中文:
定理 toFun_eq_coe
  结论: f.toFun = ⇑f
  证明: rfl

@[simp]
-/
theorem toFun_eq_coe : f.toFun = ⇑f :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : (forall i, M₁ i) -> M₂) (h₁ h₂)
  statement: ⇑(⟨f, h₁, h₂⟩ : MultilinearMap R M₁ M₂) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : (对任意 i, M₁ i) -> M₂) (h₁ h₂)
  结论: ⇑(⟨f, h₁, h₂⟩ : 多重线性映射 R M₁ M₂) = f
  证明: rfl
-/
theorem coe_mk (f : (forall i, M₁ i) -> M₂) (h₁ h₂) : ⇑(⟨f, h₁, h₂⟩ : MultilinearMap R M₁ M₂) = f :=
  rfl

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : MultilinearMap R M₁ M₂} (h : f = g) (x : forall i, M₁ i)
  statement: f x = g x
  proof: DFunLike.congr_fun h x

nonrec theorem congr_arg (f : MultilinearMap R M₁ M₂) {x y : forall i, M₁ i} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

中文:
定理 congr_fun
  条件: {f g : 多重线性映射 R M₁ M₂} (h : f = g) (x : 对任意 i, M₁ i)
  结论: f x = g x
  证明: DFunLike.congr_fun h x

nonrec theorem congr_arg (f : MultilinearMap R M₁ M₂) {x y : forall i, M₁ i} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
theorem congr_fun {f g : MultilinearMap R M₁ M₂} (h : f = g) (x : forall i, M₁ i) : f x = g x :=
  DFunLike.congr_fun h x

nonrec theorem congr_arg (f : MultilinearMap R M₁ M₂) {x y : forall i, M₁ i} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective ((↑) : MultilinearMap R M₁ M₂ -> (forall i, M₁ i) -> M₂)
  proof: DFunLike.coe_injective

@[norm_cast]

中文:
定理 coe_injective
  结论: 单射 ((↑) : 多重线性映射 R M₁ M₂ -> (对任意 i, M₁ i) -> M₂)
  证明: DFunLike.coe_injective

@[norm_cast]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective : Injective ((↑) : MultilinearMap R M₁ M₂ -> (forall i, M₁ i) -> M₂) :=
  DFunLike.coe_injective

@[norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {f g : MultilinearMap R M₁ M₂}
  statement: (f : (forall i, M₁ i) -> M₂) = g ↔ f = g
  proof: DFunLike.coe_fn_eq

@[ext]

中文:
定理 coe_inj
  条件: {f g : 多重线性映射 R M₁ M₂}
  结论: (f : (对任意 i, M₁ i) -> M₂) = g ↔ f = g
  证明: DFunLike.coe_fn_eq

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_fn_eq, coe_fn_eq
-/
theorem coe_inj {f g : MultilinearMap R M₁ M₂} : (f : (forall i, M₁ i) -> M₂) = g ↔ f = g :=
  DFunLike.coe_fn_eq

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f f' : MultilinearMap R M₁ M₂} (H : forall x, f x = f' x)
  statement: f = f'
  proof: DFunLike.ext _ _ H

@[simp]

中文:
定理 ext
  条件: {f f' : 多重线性映射 R M₁ M₂} (H : 对任意 x, f x = f' x)
  结论: f = f'
  证明: DFunLike.ext _ _ H

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ H

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : MultilinearMap R M₁ M₂) (h₁ h₂)
  proof: rfl

@[simp]

中文:
定理 mk_coe
  条件: (f : 多重线性映射 R M₁ M₂) (h₁ h₂)
  证明: rfl

@[simp]
-/
theorem mk_coe (f : MultilinearMap R M₁ M₂) (h₁ h₂) :
    (⟨f, h₁, h₂⟩ : MultilinearMap R M₁ M₂) = f := rfl

@[simp]
/--
theorem `map_update_add` / 定理 `map_update_add`

English:
theorem map_update_add
  given: [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x y : M₁ i)
  proof: f.map_update_add' m i x y

中文:
定理 map_update_add
  条件: [DecidableEq ι] (m : 对任意 i, M₁ i) (i : ι) (x y : M₁ i)
  证明: f.map_update_add' m i x y
-/
protected theorem map_update_add [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_update_add' m i x y

/-- Earlier, this name was used by what is now called `MultilinearMap.map_update_smul_left`. -/
@[simp]
/--
theorem `map_update_smul` / 定理 `map_update_smul`

English:
theorem map_update_smul
  given: [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (c : R) (x : M₁ i)
  proof: f.map_update_smul' m i c x

中文:
定理 map_update_smul
  条件: [DecidableEq ι] (m : 对任意 i, M₁ i) (i : ι) (c : R) (x : M₁ i)
  证明: f.map_update_smul' m i c x
-/
protected theorem map_update_smul [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (c : R) (x : M₁ i) :
    f (update m i (c • x)) = c • f (update m i x) :=
  f.map_update_smul' m i c x

/--
theorem `map_coord_zero` / 定理 `map_coord_zero`

English:
theorem map_coord_zero
  given: {m : forall i, M₁ i} (i : ι) (h : m i = 0)
  statement: f m = 0
  proof: by
  classical
    have : (0 : R) • (0 : M₁ i) = 0 := by simp
    rw [← update_eq_self i m]; rw [h]; rw [← this]; rw [f.map_update_smul]; rw [zero_smul]

@[simp]

中文:
定理 map_coord_zero
  条件: {m : 对任意 i, M₁ i} (i : ι) (h : m i = 0)
  结论: f m = 0
  证明: by
  classical
    have : (0 : R) • (0 : M₁ i) = 0 := by simp
    rw [← update_eq_self i m]; rw [h]; rw [← this]; rw [f.map_update_smul]; rw [zero_smul]

@[simp]

Depends on / 依赖: classical, f.map_update_smul, map_update_smul, update_eq_self, zero_smul
-/
theorem map_coord_zero {m : forall i, M₁ i} (i : ι) (h : m i = 0) : f m = 0 := by
  classical
    have : (0 : R) • (0 : M₁ i) = 0 := by simp
    rw [← update_eq_self i m]; rw [h]; rw [← this]; rw [f.map_update_smul]; rw [zero_smul]

@[simp]
/--
theorem `map_update_zero` / 定理 `map_update_zero`

English:
theorem map_update_zero
  given: [DecidableEq ι] (m : forall i, M₁ i) (i : ι)
  statement: f (update m i 0) = 0
  proof: f.map_coord_zero i (update_self i 0 m)

@[simp]

中文:
定理 map_update_zero
  条件: [DecidableEq ι] (m : 对任意 i, M₁ i) (i : ι)
  结论: f (update m i 0) = 0
  证明: f.map_coord_zero i (update_self i 0 m)

@[simp]

Depends on / 依赖: f.map_coord_zero, map_coord_zero, update_self
-/
theorem map_update_zero [DecidableEq ι] (m : forall i, M₁ i) (i : ι) : f (update m i 0) = 0 :=
  f.map_coord_zero i (update_self i 0 m)

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: [Nonempty ι]
  statement: f 0 = 0
  proof: by
  obtain ⟨i, _⟩ : exists i : ι, i in Set.univ := Set.exists_mem_of_nonempty ι
  exact map_coord_zero f i rfl

中文:
定理 map_zero
  条件: [非空 ι]
  结论: f 0 = 0
  证明: by
  obtain ⟨i, _⟩ : exists i : ι, i in Set.univ := Set.exists_mem_of_nonempty ι
  exact map_coord_zero f i rfl

Depends on / 依赖: Set.exists_mem_of_nonempty, Set.univ, exists_mem_of_nonempty, map_coord_zero
-/
theorem map_zero [Nonempty ι] : f 0 = 0 := by
  obtain ⟨i, _⟩ : exists i : ι, i in Set.univ := Set.exists_mem_of_nonempty ι
  exact map_coord_zero f i rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (MultilinearMap R M₁ M₂)
  body: ⟨fun f f' =>
    ⟨fun x => f x + f' x, fun m i x y => by simp [add_left_comm, add_assoc], fun m i c x => by
      simp [smul_add]⟩⟩

中文:
实例 :
  签名: 加法 (多重线性映射 R M₁ M₂)
  定义体: ⟨fun f f' =>
    ⟨fun x => f x + f' x, fun m i x y => by simp [add_left_comm, add_assoc], fun m i c x => by
      simp [smul_add]⟩⟩

Depends on / 依赖: add_assoc, add_left_comm, smul_add
-/
instance : Add (MultilinearMap R M₁ M₂) :=
  ⟨fun f f' =>
    ⟨fun x => f x + f' x, fun m i x y => by simp [add_left_comm, add_assoc], fun m i c x => by
      simp [smul_add]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply (MultilinearMap R M₁ M₂) (forall i, M₁ i) M₂
  body: rfl

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply

中文:
实例 :
  签名: 是加法Apply (多重线性映射 R M₁ M₂) (对任意 i, M₁ i) M₂
  定义体: rfl

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply
-/
instance : IsAddApply (MultilinearMap R M₁ M₂) (forall i, M₁ i) M₂ where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (MultilinearMap R M₁ M₂)
  body: ⟨⟨fun _ => 0, fun _ _ _ _ => by simp, fun _ _ c _ => by simp⟩⟩

中文:
实例 :
  签名: 零 (多重线性映射 R M₁ M₂)
  定义体: ⟨⟨fun _ => 0, fun _ _ _ _ => by simp, fun _ _ c _ => by simp⟩⟩
-/
instance : Zero (MultilinearMap R M₁ M₂) :=
  ⟨⟨fun _ => 0, fun _ _ _ _ => by simp, fun _ _ c _ => by simp⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply (MultilinearMap R M₁ M₂) (forall i, M₁ i) M₂
  body: rfl

中文:
实例 :
  签名: 是ZeroApply (多重线性映射 R M₁ M₂) (对任意 i, M₁ i) M₂
  定义体: rfl
-/
instance : IsZeroApply (MultilinearMap R M₁ M₂) (forall i, M₁ i) M₂ where
  zero_apply _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (MultilinearMap R M₁ M₂)
  body: ⟨0⟩

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply

中文:
实例 :
  签名: 可居 (多重线性映射 R M₁ M₂)
  定义体: ⟨0⟩

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply
-/
instance : Inhabited (MultilinearMap R M₁ M₂) :=
  ⟨0⟩

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply

section SMul

variable [DistribSMul S M₂] [SMulCommClass R S M₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul S (MultilinearMap R M₁ M₂)
  body: ⟨fun c f =>
    ⟨fun m => c • f m, fun m i x y => by simp [smul_add], fun l i x d => by
      simp [← smul_comm x c (_ : M₂)]⟩⟩

中文:
实例 :
  签名: 标量乘法 S (多重线性映射 R M₁ M₂)
  定义体: ⟨fun c f =>
    ⟨fun m => c • f m, fun m i x y => by simp [smul_add], fun l i x d => by
      simp [← smul_comm x c (_ : M₂)]⟩⟩

Depends on / 依赖: smul_add, smul_comm
-/
instance : SMul S (MultilinearMap R M₁ M₂) :=
  ⟨fun c f =>
    ⟨fun m => c • f m, fun m i x y => by simp [smul_add], fun l i x d => by
      simp [← smul_comm x c (_ : M₂)]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply S (MultilinearMap R M₁ M₂) (forall i, M₁ i) M₂
  body: rfl

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply

@[deprecated (since := "2026-06-10")] alias coe_smul := FunLike.coe_smul

中文:
实例 :
  签名: 是SMulApply S (多重线性映射 R M₁ M₂) (对任意 i, M₁ i) M₂
  定义体: rfl

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply

@[deprecated (since := "2026-06-10")] alias coe_smul := FunLike.coe_smul
-/
instance : IsSMulApply S (MultilinearMap R M₁ M₂) (forall i, M₁ i) M₂ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply

@[deprecated (since := "2026-06-10")] alias coe_smul := FunLike.coe_smul

end SMul

-- The `AddMonoid` instance exists to help speedup unification
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoid (MultilinearMap R M₁ M₂)
  body: fast_instance% FunLike.addMonoid

中文:
实例 :
  签名: 加法幺半群 (多重线性映射 R M₁ M₂)
  定义体: fast_instance% FunLike.addMonoid

Depends on / 依赖: FunLike, FunLike.addMonoid, addMonoid, fast_instance
-/
instance : AddMonoid (MultilinearMap R M₁ M₂) := fast_instance% FunLike.addMonoid

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: : AddCommMonoid (MultilinearMap R M₁ M₂)
  body: fast_instance%
  FunLike.addCommMonoid

@[deprecated (since := "2026-06-10")] alias coeAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-10")] alias coeAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-10")] alias coe_sum := FunLike.coe_sum



中文:
实例 addCommMonoid
  签名: : 加法交换幺半群 (多重线性映射 R M₁ M₂)
  定义体: fast_instance%
  FunLike.addCommMonoid

@[deprecated (since := "2026-06-10")] alias coeAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-10")] alias coeAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-10")] alias coe_sum := FunLike.coe_sum



Depends on / 依赖: fast_instance
-/
instance addCommMonoid : AddCommMonoid (MultilinearMap R M₁ M₂) := fast_instance%
  FunLike.addCommMonoid

@[deprecated (since := "2026-06-10")] alias coeAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-10")] alias coeAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-10")] alias coe_sum := FunLike.coe_sum

@[deprecated (since := "2026-06-10")] protected alias sum_apply := _root_.sum_apply

/-- If `f` is a multilinear map, then `f.toLinearMap m i` is the linear map obtained by fixing all
coordinates but `i` equal to those of `m`, and varying the `i`-th coordinate. -/
@[simps]
/--
Definition of `toLinearMap` / `toLinearMap` 的定义

English:
definition toLinearMap
  signature: [DecidableEq ι] (m : forall i, M₁ i) (i : ι)
  body: f (update m i x)
  map_add' x y := by simp
  map_smul' c x := by simp

中文:
定义 toLinearMap
  签名: [DecidableEq ι] (m : 对任意 i, M₁ i) (i : ι)
  定义体: f (update m i x)
  map_add' x y := by simp
  map_smul' c x := by simp

Depends on / 依赖: update
-/
def toLinearMap [DecidableEq ι] (m : forall i, M₁ i) (i : ι) : M₁ i ->ₗ[R] M₂ where
  toFun x := f (update m i x)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The Cartesian product of two multilinear maps, as a multilinear map. -/
@[simps]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : MultilinearMap R M₁ M₂) (g : MultilinearMap R M₁ M₃)
  body: (f m, g m)
  map_update_add' m i x y := by simp
  map_update_smul' m i c x := by simp

中文:
定义 乘积
  签名: (f : 多重线性映射 R M₁ M₂) (g : 多重线性映射 R M₁ M₃)
  定义体: (f m, g m)
  map_update_add' m i x y := by simp
  map_update_smul' m i c x := by simp
-/
def prod (f : MultilinearMap R M₁ M₂) (g : MultilinearMap R M₁ M₃) :
    MultilinearMap R M₁ (M₂ × M₃) where
  toFun m := (f m, g m)
  map_update_add' m i x y := by simp
  map_update_smul' m i c x := by simp

/-- Combine a family of multilinear maps with the same domain and codomains `M' i` into a
multilinear map taking values in the space of functions `∀ i, M' i`. -/
@[simps]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] [forall i, Module R (M' i)]
  body: f i m
  map_update_add' _ _ _ _ := funext fun j => (f j).map_update_add _ _ _ _
  map_update_smul' _ _ _ _ := funext fun j => (f j).map_update_smul _ _ _ _

中文:
定义 pi
  签名: {ι' : 类型} {M' : ι' -> 类型} [对任意 i, 加法交换幺半群 (M' i)] [对任意 i, 模 R (M' i)]
  定义体: f i m
  map_update_add' _ _ _ _ := funext fun j => (f j).map_update_add _ _ _ _
  map_update_smul' _ _ _ _ := funext fun j => (f j).map_update_smul _ _ _ _
-/
def pi {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] [forall i, Module R (M' i)]
    (f : forall i, MultilinearMap R M₁ (M' i)) : MultilinearMap R M₁ (forall i, M' i) where
  toFun m i := f i m
  map_update_add' _ _ _ _ := funext fun j => (f j).map_update_add _ _ _ _
  map_update_smul' _ _ _ _ := funext fun j => (f j).map_update_smul _ _ _ _

section

variable (R M₂ M₃)

/-- Equivalence between linear maps `M₂ →ₗ[R] M₃` and one-multilinear maps. -/
@[simps]
/--
Definition of `ofSubsingleton` / `ofSubsingleton` 的定义

English:
definition ofSubsingleton
  signature: [Subsingleton ι] (i : ι)
  body: { toFun := fun x => f (x i)
      map_update_add' := by intros; simp [update_eq_const_of_subsingleton]
      map_update_smul' := by intros; simp [update_eq_const_of_subsingleton] }
  invFun f :=
    { toFun := fun x => f fun _ => x
      map_add' := fun x y => by
        simpa [update_eq_const_of_su

中文:
定义 ofSubsingleton
  签名: [子单例 ι] (i : ι)
  定义体: { toFun := fun x => f (x i)
      map_update_add' := by intros; simp [update_eq_const_of_subsingleton]
      map_update_smul' := by intros; simp [update_eq_const_of_subsingleton] }
  invFun f :=
    { toFun := fun x => f fun _ => x
      map_add' := fun x y => by
        simpa [update_eq_const_of_su

Depends on / 依赖: congr_arg, eq_const_of_subsingleton, f.map_update_add, f.map_update_smul, intros, invFun, map_add, map_smul, map_update_add, map_update_smul, right_inv, update_eq_const_of_subsingleton
-/
def ofSubsingleton [Subsingleton ι] (i : ι) :
    (M₂ ->ₗ[R] M₃) ≃ MultilinearMap R (fun _ : ι => M₂) M₃ where
  toFun f :=
    { toFun := fun x => f (x i)
      map_update_add' := by intros; simp [update_eq_const_of_subsingleton]
      map_update_smul' := by intros; simp [update_eq_const_of_subsingleton] }
  invFun f :=
    { toFun := fun x => f fun _ => x
      map_add' := fun x y => by
        simpa [update_eq_const_of_subsingleton] using! f.map_update_add 0 i x y
      map_smul' := fun c x => by
        simpa [update_eq_const_of_subsingleton] using! f.map_update_smul 0 i c x }
  right_inv f := by ext x; refine congr_arg f ?_; exact (eq_const_of_subsingleton _ _).symm

variable (M₁) {M₂}

/-- The constant map is multilinear when `ι` is empty. -/
@[simps -fullyApplied]
/--
Definition of `constOfIsEmpty` / `constOfIsEmpty` 的定义

English:
definition constOfIsEmpty
  signature: [IsEmpty ι] (m : M₂)
  body: Function.const _ m
  map_update_add' _ := isEmptyElim
  map_update_smul' _ := isEmptyElim

中文:
定义 constOfIsEmpty
  签名: [是空 ι] (m : M₂)
  定义体: Function.const _ m
  map_update_add' _ := isEmptyElim
  map_update_smul' _ := isEmptyElim

Depends on / 依赖: Function, Function.const
-/
def constOfIsEmpty [IsEmpty ι] (m : M₂) : MultilinearMap R M₁ M₂ where
  toFun := Function.const _ m
  map_update_add' _ := isEmptyElim
  map_update_smul' _ := isEmptyElim

end

/--
Definition of `restr` / `restr` 的定义

English:
definition restr
  signature: {k n : Nat} (f : MultilinearMap R (fun _ : Fin n => M') M₂) (s : Finset (Fin n))
  body: f fun j => if h : j in s then v ((s.orderIsoOfFin hk).symm ⟨j, h⟩) else z
  map_update_add' := by
    simp [dite_comp_equiv_update (s.orderIsoOfFin hk).symm]
  map_update_smul' := by
    simp [dite_comp_equiv_update (s.orderIsoOfFin hk).symm]

中文:
定义 restr
  签名: {k n : 自然数} (f : 多重线性映射 R (fun _ : 有限集 n => M') M₂) (s : 有限集 (有限集 n))
  定义体: f fun j => if h : j in s then v ((s.orderIsoOfFin hk).symm ⟨j, h⟩) else z
  map_update_add' := by
    simp [dite_comp_equiv_update (s.orderIsoOfFin hk).symm]
  map_update_smul' := by
    simp [dite_comp_equiv_update (s.orderIsoOfFin hk).symm]

Depends on / 依赖: orderIsoOfFin, s.orderIsoOfFin
-/
def restr {k n : Nat} (f : MultilinearMap R (fun _ : Fin n => M') M₂) (s : Finset (Fin n))
    (hk : #s = k) (z : M') : MultilinearMap R (fun _ : Fin k => M') M₂ where
  toFun v := f fun j => if h : j in s then v ((s.orderIsoOfFin hk).symm ⟨j, h⟩) else z
  map_update_add' := by
    simp [dite_comp_equiv_update (s.orderIsoOfFin hk).symm]
  map_update_smul' := by
    simp [dite_comp_equiv_update (s.orderIsoOfFin hk).symm]

/--
theorem `cons_add` / 定理 `cons_add`

English:
theorem cons_add
  given: (f : MultilinearMap R M M₂) (m : forall i : Fin n, M i.succ) (x y : M 0)
  proof: by
  simp_rw [← update_cons_zero x m (x + y), f.map_update_add, update_cons_zero]

中文:
定理 cons_add
  条件: (f : 多重线性映射 R M M₂) (m : 对任意 i : 有限集 n, M i.succ) (x y : M 0)
  证明: by
  simp_rw [← update_cons_zero x m (x + y), f.map_update_add, update_cons_zero]

Depends on / 依赖: f.map_update_add, map_update_add, simp_rw, update_cons_zero
-/
theorem cons_add (f : MultilinearMap R M M₂) (m : forall i : Fin n, M i.succ) (x y : M 0) :
    f (cons (x + y) m) = f (cons x m) + f (cons y m) := by
  simp_rw [← update_cons_zero x m (x + y), f.map_update_add, update_cons_zero]

/--
theorem `cons_smul` / 定理 `cons_smul`

English:
theorem cons_smul
  given: (f : MultilinearMap R M M₂) (m : forall i : Fin n, M i.succ) (c : R) (x : M 0)
  proof: by
  simp_rw [← update_cons_zero x m (c • x), f.map_update_smul, update_cons_zero]

中文:
定理 cons_smul
  条件: (f : 多重线性映射 R M M₂) (m : 对任意 i : 有限集 n, M i.succ) (c : R) (x : M 0)
  证明: by
  simp_rw [← update_cons_zero x m (c • x), f.map_update_smul, update_cons_zero]

Depends on / 依赖: f.map_update_smul, map_update_smul, simp_rw, update_cons_zero
-/
theorem cons_smul (f : MultilinearMap R M M₂) (m : forall i : Fin n, M i.succ) (c : R) (x : M 0) :
    f (cons (c • x) m) = c • f (cons x m) := by
  simp_rw [← update_cons_zero x m (c • x), f.map_update_smul, update_cons_zero]

/--
theorem `snoc_add` / 定理 `snoc_add`

English:
theorem snoc_add
  statement: (f : MultilinearMap R M M₂)
  proof: by
  simp_rw [← update_snoc_last x m (x + y), f.map_update_add, update_snoc_last]

中文:
定理 snoc_add
  结论: (f : 多重线性映射 R M M₂)
  证明: by
  simp_rw [← update_snoc_last x m (x + y), f.map_update_add, update_snoc_last]

Depends on / 依赖: f.map_update_add, map_update_add, simp_rw, update_snoc_last
-/
theorem snoc_add (f : MultilinearMap R M M₂)
    (m : forall i : Fin n, M (castSucc i)) (x y : M (last n)) :
    f (snoc m (x + y)) = f (snoc m x) + f (snoc m y) := by
  simp_rw [← update_snoc_last x m (x + y), f.map_update_add, update_snoc_last]

/--
theorem `snoc_smul` / 定理 `snoc_smul`

English:
theorem snoc_smul
  statement: (f : MultilinearMap R M M₂) (m : forall i : Fin n, M (castSucc i)) (c : R)
  proof: by
  simp_rw [← update_snoc_last x m (c • x), f.map_update_smul, update_snoc_last]

中文:
定理 snoc_smul
  结论: (f : 多重线性映射 R M M₂) (m : 对任意 i : 有限集 n, M (castSucc i)) (c : R)
  证明: by
  simp_rw [← update_snoc_last x m (c • x), f.map_update_smul, update_snoc_last]

Depends on / 依赖: f.map_update_smul, map_update_smul, simp_rw, update_snoc_last
-/
theorem snoc_smul (f : MultilinearMap R M M₂) (m : forall i : Fin n, M (castSucc i)) (c : R)
    (x : M (last n)) : f (snoc m (c • x)) = c • f (snoc m x) := by
  simp_rw [← update_snoc_last x m (c • x), f.map_update_smul, update_snoc_last]

/--
theorem `map_insertNth_add` / 定理 `map_insertNth_add`

English:
theorem map_insertNth_add
  statement: (f : MultilinearMap R M M₂) (p : Fin (n + 1)) (m : forall i, M (p.succAbove i))
  proof: by
  simpa using f.map_update_add (p.insertNth 0 m) p x y

中文:
定理 map_insertNth_add
  结论: (f : 多重线性映射 R M M₂) (p : 有限集 (n + 1)) (m : 对任意 i, M (p.succAbove i))
  证明: by
  simpa using f.map_update_add (p.insertNth 0 m) p x y

Depends on / 依赖: f.map_update_add, insertNth, map_update_add, p.insertNth
-/
theorem map_insertNth_add (f : MultilinearMap R M M₂) (p : Fin (n + 1)) (m : forall i, M (p.succAbove i))
    (x y : M p) : f (p.insertNth (x + y) m) = f (p.insertNth x m) + f (p.insertNth y m) := by
  simpa using f.map_update_add (p.insertNth 0 m) p x y

/--
theorem `map_insertNth_smul` / 定理 `map_insertNth_smul`

English:
theorem map_insertNth_smul
  statement: (f : MultilinearMap R M M₂) (p : Fin (n + 1))
  proof: by
  simpa using f.map_update_smul (p.insertNth 0 m) p c x

中文:
定理 map_insertNth_smul
  结论: (f : 多重线性映射 R M M₂) (p : 有限集 (n + 1))
  证明: by
  simpa using f.map_update_smul (p.insertNth 0 m) p c x

Depends on / 依赖: f.map_update_smul, insertNth, map_update_smul, p.insertNth
-/
theorem map_insertNth_smul (f : MultilinearMap R M M₂) (p : Fin (n + 1))
    (m : forall i, M (p.succAbove i)) (c : R) (x : M p) :
    f (p.insertNth (c • x) m) = c • f (p.insertNth x m) := by
  simpa using f.map_update_smul (p.insertNth 0 m) p c x

section

variable [forall i, AddCommMonoid (M₁' i)] [forall i, Module R (M₁' i)]
variable [forall i, AddCommMonoid (M₁'' i)] [forall i, Module R (M₁'' i)]

/--
Definition of `compLinearMap` / `compLinearMap` 的定义

English:
definition compLinearMap
  signature: (g : MultilinearMap R M₁' M₂) (f : forall i, M₁ i ->ₗ[R] M₁' i)
  body: g fun i => f i (m i)
  map_update_add' m i x y := by
    have : forall j z, f j (update m i z j) = update (fun k => f k (m k)) i (f i z) j := fun j z =>
      Function.apply_update (fun k => f k) _ _ _ _
    simp [this]
  map_update_smul' m i c x := by
    have : forall j z, f j (update m i z j) = u

中文:
定义 compLinearMap
  签名: (g : 多重线性映射 R M₁' M₂) (f : 对任意 i, M₁ i ->ₗ[R] M₁' i)
  定义体: g fun i => f i (m i)
  map_update_add' m i x y := by
    have : forall j z, f j (update m i z j) = update (fun k => f k (m k)) i (f i z) j := fun j z =>
      Function.apply_update (fun k => f k) _ _ _ _
    simp [this]
  map_update_smul' m i c x := by
    have : forall j z, f j (update m i z j) = u
-/
def compLinearMap (g : MultilinearMap R M₁' M₂) (f : forall i, M₁ i ->ₗ[R] M₁' i) :
    MultilinearMap R M₁ M₂ where
  toFun m := g fun i => f i (m i)
  map_update_add' m i x y := by
    have : forall j z, f j (update m i z j) = update (fun k => f k (m k)) i (f i z) j := fun j z =>
      Function.apply_update (fun k => f k) _ _ _ _
    simp [this]
  map_update_smul' m i c x := by
    have : forall j z, f j (update m i z j) = update (fun k => f k (m k)) i (f i z) j := fun j z =>
      Function.apply_update (fun k => f k) _ _ _ _
    simp [this]

@[simp]
/--
theorem `compLinearMap_apply` / 定理 `compLinearMap_apply`

English:
theorem compLinearMap_apply
  statement: (g : MultilinearMap R M₁' M₂) (f : forall i, M₁ i ->ₗ[R] M₁' i)
  proof: rfl

中文:
定理 compLinearMap_apply
  结论: (g : 多重线性映射 R M₁' M₂) (f : 对任意 i, M₁ i ->ₗ[R] M₁' i)
  证明: rfl
-/
theorem compLinearMap_apply (g : MultilinearMap R M₁' M₂) (f : forall i, M₁ i ->ₗ[R] M₁' i)
    (m : forall i, M₁ i) : g.compLinearMap f m = g fun i => f i (m i) :=
  rfl

/--
theorem `compLinearMap_assoc` / 定理 `compLinearMap_assoc`

English:
theorem compLinearMap_assoc
  statement: (g : MultilinearMap R M₁'' M₂) (f₁ : forall i, M₁' i ->ₗ[R] M₁'' i)
  proof: rfl

中文:
定理 compLinearMap_assoc
  结论: (g : 多重线性映射 R M₁'' M₂) (f₁ : 对任意 i, M₁' i ->ₗ[R] M₁'' i)
  证明: rfl
-/
theorem compLinearMap_assoc (g : MultilinearMap R M₁'' M₂) (f₁ : forall i, M₁' i ->ₗ[R] M₁'' i)
    (f₂ : forall i, M₁ i ->ₗ[R] M₁' i) :
    (g.compLinearMap f₁).compLinearMap f₂ = g.compLinearMap fun i => f₁ i ∘ₗ f₂ i :=
  rfl

/-- Composing the zero multilinear map with a linear map in each argument. -/
@[simp]
/--
theorem `zero_compLinearMap` / 定理 `zero_compLinearMap`

English:
theorem zero_compLinearMap
  given: (f : forall i, M₁ i ->ₗ[R] M₁' i)
  proof: ext fun _ => rfl

中文:
定理 zero_compLinearMap
  条件: (f : 对任意 i, M₁ i ->ₗ[R] M₁' i)
  证明: ext fun _ => rfl
-/
theorem zero_compLinearMap (f : forall i, M₁ i ->ₗ[R] M₁' i) :
    (0 : MultilinearMap R M₁' M₂).compLinearMap f = 0 :=
  ext fun _ => rfl

/-- Composing a multilinear map with the identity linear map in each argument. -/
@[simp]
/--
theorem `compLinearMap_id` / 定理 `compLinearMap_id`

English:
theorem compLinearMap_id
  given: (g : MultilinearMap R M₁' M₂)
  proof: ext fun _ => rfl

中文:
定理 compLinearMap_id
  条件: (g : 多重线性映射 R M₁' M₂)
  证明: ext fun _ => rfl
-/
theorem compLinearMap_id (g : MultilinearMap R M₁' M₂) :
    (g.compLinearMap fun _ => LinearMap.id) = g :=
  ext fun _ => rfl

/--
theorem `compLinearMap_injective` / 定理 `compLinearMap_injective`

English:
theorem compLinearMap_injective
  given: (f : forall i, M₁ i ->ₗ[R] M₁' i) (hf : forall i, Surjective (f i))
  proof: fun g₁ g₂ h =>
  ext fun x => by
    simpa [fun i => surjInv_eq (hf i)]
      using MultilinearMap.ext_iff.mp h fun i => surjInv (hf i) (x i)

中文:
定理 compLinearMap_injective
  条件: (f : 对任意 i, M₁ i ->ₗ[R] M₁' i) (hf : 对任意 i, 满射 (f i))
  证明: fun g₁ g₂ h =>
  ext fun x => by
    simpa [fun i => surjInv_eq (hf i)]
      using MultilinearMap.ext_iff.mp h fun i => surjInv (hf i) (x i)
-/
theorem compLinearMap_injective (f : forall i, M₁ i ->ₗ[R] M₁' i) (hf : forall i, Surjective (f i)) :
    Injective fun g : MultilinearMap R M₁' M₂ => g.compLinearMap f := fun g₁ g₂ h =>
  ext fun x => by
    simpa [fun i => surjInv_eq (hf i)]
      using MultilinearMap.ext_iff.mp h fun i => surjInv (hf i) (x i)

/--
theorem `compLinearMap_inj` / 定理 `compLinearMap_inj`

English:
theorem compLinearMap_inj
  statement: (f : forall i, M₁ i ->ₗ[R] M₁' i) (hf : forall i, Surjective (f i))
  proof: (compLinearMap_injective _ hf).eq_iff

中文:
定理 compLinearMap_inj
  结论: (f : 对任意 i, M₁ i ->ₗ[R] M₁' i) (hf : 对任意 i, 满射 (f i))
  证明: (compLinearMap_injective _ hf).eq_iff

Depends on / 依赖: compLinearMap_injective, eq_iff
-/
theorem compLinearMap_inj (f : forall i, M₁ i ->ₗ[R] M₁' i) (hf : forall i, Surjective (f i))
    (g₁ g₂ : MultilinearMap R M₁' M₂) : g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂ :=
  (compLinearMap_injective _ hf).eq_iff

/-- Composing a multilinear map with a linear equiv on each argument gives the zero map
if and only if the multilinear map is the zero map. -/
@[simp]
/--
theorem `comp_linearEquiv_eq_zero_iff` / 定理 `comp_linearEquiv_eq_zero_iff`

English:
theorem comp_linearEquiv_eq_zero_iff
  given: (g : MultilinearMap R M₁' M₂) (f : forall i, M₁ i ≃ₗ[R] M₁' i)
  proof: by
  set f' := fun i => (f i : M₁ i ->ₗ[R] M₁' i)
  rw [← zero_compLinearMap f']; rw [compLinearMap_inj f' fun i => (f i).surjective]

中文:
定理 comp_linearEquiv_eq_zero_iff
  条件: (g : 多重线性映射 R M₁' M₂) (f : 对任意 i, M₁ i ≃ₗ[R] M₁' i)
  证明: by
  set f' := fun i => (f i : M₁ i ->ₗ[R] M₁' i)
  rw [← zero_compLinearMap f']; rw [compLinearMap_inj f' fun i => (f i).surjective]

Depends on / 依赖: compLinearMap_inj, surjective, zero_compLinearMap
-/
theorem comp_linearEquiv_eq_zero_iff (g : MultilinearMap R M₁' M₂) (f : forall i, M₁ i ≃ₗ[R] M₁' i) :
    (g.compLinearMap fun i => (f i : M₁ i ->ₗ[R] M₁' i)) = 0 ↔ g = 0 := by
  set f' := fun i => (f i : M₁ i ->ₗ[R] M₁' i)
  rw [← zero_compLinearMap f']; rw [compLinearMap_inj f' fun i => (f i).surjective]


section compMultilinear

variable {β : ι -> Type*}
variable {N : (i : ι) -> (b : β i) -> Type*}
variable [forall i, forall b, AddCommMonoid (N i b)] [forall i, forall b, Module R (N i b)]

/-- Composition of multilinear maps. If `g` is multilinear, and if for every `i : ι`, we have a
multilinear map `f i` with index type `β i`, then `m ↦ g (f₁ m_11 m_12 ...) (f₂ m_21 m_22 ...) ...`
is multilinear with index type `(Σ i, β i)`. -/
@[simps]
/--
Definition of `compMultilinearMap` / `compMultilinearMap` 的定义

English:
definition compMultilinearMap
  signature: (g : MultilinearMap R M₁ M₂) (f : (i : ι) -> MultilinearMap R (N i) (M₁ i))
  body: g fun i => f i (Sigma.curry m i)
  map_update_add' {hDecEqSigma} := by
    classical
    simp +instances [Subsingleton.elim hDecEqSigma Sigma.instDecidableEqSigma,
      Sigma.curry_update, Function.apply_update (fun i => f i)]
  map_update_smul' {hDecEqSigma} := by
    classical
    simp +instances

中文:
定义 compMultilinearMap
  签名: (g : 多重线性映射 R M₁ M₂) (f : (i : ι) -> 多重线性映射 R (N i) (M₁ i))
  定义体: g fun i => f i (Sigma.curry m i)
  map_update_add' {hDecEqSigma} := by
    classical
    simp +instances [Subsingleton.elim hDecEqSigma Sigma.instDecidableEqSigma,
      Sigma.curry_update, Function.apply_update (fun i => f i)]
  map_update_smul' {hDecEqSigma} := by
    classical
    simp +instances

Depends on / 依赖: Sigma.curry
-/
def compMultilinearMap (g : MultilinearMap R M₁ M₂) (f : (i : ι) -> MultilinearMap R (N i) (M₁ i)) :
    MultilinearMap R (fun j : Σ i, β i => N j.fst j.snd) M₂ where
  toFun m := g fun i => f i (Sigma.curry m i)
  map_update_add' {hDecEqSigma} := by
    classical
    simp +instances [Subsingleton.elim hDecEqSigma Sigma.instDecidableEqSigma,
      Sigma.curry_update, Function.apply_update (fun i => f i)]
  map_update_smul' {hDecEqSigma} := by
    classical
    simp +instances [Subsingleton.elim hDecEqSigma Sigma.instDecidableEqSigma,
      Sigma.curry_update, Function.apply_update (fun i => f i)]

end compMultilinear

end

/--
theorem `map_piecewise_add` / 定理 `map_piecewise_add`

English:
theorem map_piecewise_add
  given: [DecidableEq ι] (m m' : forall i, M₁ i) (t : Finset ι)
  proof: by
  revert m'
  refine Finset.induction_on t (by simp) ?_
  intro i t hit Hrec m'
  have A : (insert i t).piecewise (m + m') m' = update (t.piecewise (m + m') m') i (m i + m' i) :=
    t.piecewise_insert _ _ _
  have B : update (t.piecewise (m + m') m') i (m' i) = t.piecewise (m + m') m' := by
    

中文:
定理 map_piecewise_add
  条件: [DecidableEq ι] (m m' : 对任意 i, M₁ i) (t : 有限集 ι)
  证明: by
  revert m'
  refine Finset.induction_on t (by simp) ?_
  intro i t hit Hrec m'
  have A : (insert i t).piecewise (m + m') m' = update (t.piecewise (m + m') m') i (m i + m' i) :=
    t.piecewise_insert _ _ _
  have B : update (t.piecewise (m + m') m') i (m' i) = t.piecewise (m + m') m' := by
    

Depends on / 依赖: Finset, Finset.induction_on, induction_on, insert, piecewise, piecewise_insert, revert, t.piecewise, t.piecewise_insert, update
-/
theorem map_piecewise_add [DecidableEq ι] (m m' : forall i, M₁ i) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s in t.powerset, f (s.piecewise m m') := by
  revert m'
  refine Finset.induction_on t (by simp) ?_
  intro i t hit Hrec m'
  have A : (insert i t).piecewise (m + m') m' = update (t.piecewise (m + m') m') i (m i + m' i) :=
    t.piecewise_insert _ _ _
  have B : update (t.piecewise (m + m') m') i (m' i) = t.piecewise (m + m') m' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [hit]
    · simp [h]
  let m'' := update m' i (m i)
  have C : update (t.piecewise (m + m') m') i (m i) = t.piecewise (m + m'') m'' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [m'', hit]
    · by_cases h' : j in t <;> simp [m'', h, h']
  rw [A]; rw [f.map_update_add]; rw [B]; rw [C]; rw [Finset.sum_powerset_insert hit]; rw [Hrec]; rw [Hrec]; rw [add_comm (_ : M₂)]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  have : (insert i s).piecewise m m' = s.piecewise m m'' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [m'', Finset.notMem_of_mem_powerset_of_notMem hs hit]
    · by_cases h' : j in s <;> simp [m'', h, h']
  rw [this]

/--
theorem `map_add_univ` / 定理 `map_add_univ`

English:
theorem map_add_univ
  given: [DecidableEq ι] [Fintype ι] (m m' : forall i, M₁ i)
  proof: by
  simpa using f.map_piecewise_add m m' Finset.univ

中文:
定理 map_add_univ
  条件: [DecidableEq ι] [有限类型 ι] (m m' : 对任意 i, M₁ i)
  证明: by
  simpa using f.map_piecewise_add m m' Finset.univ

Depends on / 依赖: Finset, Finset.univ, f.map_piecewise_add, map_piecewise_add
-/
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : forall i, M₁ i) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') := by
  simpa using f.map_piecewise_add m m' Finset.univ

section ApplySum

variable {α : ι -> Type*} (g : forall i, α i -> M₁ i) (A : forall i, Finset (α i))

open Fintype Finset

/--
theorem `map_sum_finset_aux` / 定理 `map_sum_finset_aux`

English:
theorem map_sum_finset_aux
  given: [DecidableEq ι] [Fintype ι] {n : Nat} (h : (∑ i, #(A i)) = n)
  proof: by
  let := fun i => Classical.decEq (α i)
  induction n using Nat.strong_induction_on generalizing A with | h n IH =>
  -- If one of the sets is empty, then all the sums are zero
  by_cases! Ai_empty : exists i, A i = ∅
  · obtain ⟨i, hi⟩ : exists i, ∑ j in A i, g i j = 0 := Ai_empty.imp fun i hi =

中文:
定理 map_sum_finset_aux
  条件: [DecidableEq ι] [有限类型 ι] {n : 自然数} (h : (∑ i, #(A i)) = n)
  证明: by
  let := fun i => Classical.decEq (α i)
  induction n using Nat.strong_induction_on generalizing A with | h n IH =>
  -- If one of the sets is empty, then all the sums are zero
  by_cases! Ai_empty : exists i, A i = ∅
  · obtain ⟨i, hi⟩ : exists i, ∑ j in A i, g i j = 0 := Ai_empty.imp fun i hi =

Depends on / 依赖: Classical, Classical.decEq, Nat.strong_induction_on, generalizing, strong_induction_on
-/
theorem map_sum_finset_aux [DecidableEq ι] [Fintype ι] {n : Nat} (h : (∑ i, #(A i)) = n) :
    (f fun i => ∑ j in A i, g i j) = ∑ r in piFinset A, f fun i => g i (r i) := by
  let := fun i => Classical.decEq (α i)
  induction n using Nat.strong_induction_on generalizing A with | h n IH =>
  -- If one of the sets is empty, then all the sums are zero
  by_cases! Ai_empty : exists i, A i = ∅
  · obtain ⟨i, hi⟩ : exists i, ∑ j in A i, g i j = 0 := Ai_empty.imp fun i hi => by simp [hi]
    have hpi : piFinset A = ∅ := by simpa
    rw [f.map_coord_zero i hi]; rw [hpi]; rw [Finset.sum_empty]
  -- Otherwise, if all sets are at most singletons, then they are exactly singletons and the result
  -- is again straightforward
  by_cases! Ai_singleton : forall i, #(A i) <= 1
  · have Ai_card : forall i, #(A i) = 1 := by
      intro i
      have pos : #(A i) != 0 := by rw [Finset.card_ne_zero]; exact Ai_empty i
      have : #(A i) <= 1 := Ai_singleton i
      exact le_antisymm this (Nat.succ_le_of_lt (_root_.pos_iff_ne_zero.mpr pos))
    have :
      forall r : forall i, α i, r in piFinset A -> (f fun i => g i (r i)) = f fun i => ∑ j in A i, g i j := by
      intro r hr
      congr with i
      have : forall j in A i, g i j = g i (r i) := by
        intro j hj
        congr
        apply Finset.card_le_one_iff.1 (Ai_singleton i) hj
        exact mem_piFinset.mp hr i
      simp only [Finset.sum_congr rfl this, Finset.sum_const, Ai_card i, one_nsmul]
    simp only [Finset.sum_congr rfl this, Ai_card, card_piFinset, prod_const_one, one_nsmul,
      Finset.sum_const]
  -- Remains the interesting case where one of the `A i`, say `A i₀`, has cardinality at least 2.
  -- We will split into two parts `B i₀` and `C i₀` of smaller cardinality, let `B i = C i = A i`
  -- for `i ≠ i₀`, apply the inductive assumption to `B` and `C`, and add up the corresponding
  -- parts to get the sum for `A`.
  obtain ⟨i₀, hi₀⟩ : exists i, 1 < #(A i) := Ai_singleton
  obtain ⟨j₁, j₂, _, hj₂, _⟩ : exists j₁ j₂, j₁ in A i₀ ∧ j₂ in A i₀ ∧ j₁ != j₂ :=
    Finset.one_lt_card_iff.1 hi₀
  let B := Function.update A i₀ (A i₀ \ {j₂})
  let C := Function.update A i₀ {j₂}
  have B_subset_A : forall i, B i subseteq A i := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [B, Finset.sdiff_subset, update_self]
    · simp only [B, hi, update_of_ne, Ne, not_false_iff, Finset.Subset.refl]
  have C_subset_A : forall i, C i subseteq A i := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [C, hj₂, Finset.singleton_subset_iff, update_self]
    · simp only [C, hi, update_of_ne, Ne, not_false_iff, Finset.Subset.refl]
  -- split the sum at `i₀` as the sum over `B i₀` plus the sum over `C i₀`, to use additivity.
  have A_eq_BC :
    (fun i => ∑ j in A i, g i j) =
      Function.update (fun i => ∑ j in A i, g i j) i₀
        ((∑ j in B i₀, g i₀ j) + ∑ j in C i₀, g i₀ j) := by
    ext i
    by_cases hi : i = i₀
    · rw [hi, update_self]
      have : A i₀ = B i₀ union C i₀ := by
        simp only [B, C, Function.update_self, Finset.sdiff_union_self_eq_union]
        symm
        simp only [hj₂, Finset.singleton_subset_iff, Finset.union_eq_left]
      rw [this]
refine Finset.sum_union Finset.disjoint_right.2 fun j hj => ?_
      have : j = j₂ := by
        simpa [C] using hj
      rw [this]
      simp only [B, Finset.mem_sdiff, not_true, not_false_iff, Finset.mem_singleton,
        update_self, and_false]
    · simp [hi]
  have Beq :
    Function.update (fun i => ∑ j in A i, g i j) i₀ (∑ j in B i₀, g i₀ j) = fun i =>
      ∑ j in B i, g i j := by
    ext i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [update_self]
    · simp only [B, hi, update_of_ne, Ne, not_false_iff]
  have Ceq :
    Function.update (fun i => ∑ j in A i, g i j) i₀ (∑ j in C i₀, g i₀ j) = fun i =>
      ∑ j in C i, g i j := by
    ext i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [update_self]
    · simp only [C, hi, update_of_ne, Ne, not_false_iff]
  -- Express the inductive assumption for `B`
  have Brec : (f fun i => ∑ j in B i, g i j) = ∑ r in piFinset B, f fun i => g i (r i) := by
    have : ∑ i, #(B i) < ∑ i, #(A i) := by
      refine sum_lt_sum (fun i _ => card_le_card (B_subset_A i)) ⟨i₀, mem_univ _, ?_⟩
      have : {j₂} subseteq A i₀ := by simp [hj₂]
      simp only [B, Finset.card_sdiff_of_subset this, Function.update_self, Finset.card_singleton]
      exact Nat.pred_lt (ne_of_gt (lt_trans Nat.zero_lt_one hi₀))
    rw [h] at this
    exact IH _ this B rfl
  -- Express the inductive assumption for `C`
  have Crec : (f fun i => ∑ j in C i, g i j) = ∑ r in piFinset C, f fun i => g i (r i) := by
    have : (∑ i, #(C i)) < ∑ i, #(A i) :=
      Finset.sum_lt_sum (fun i _ => Finset.card_le_card (C_subset_A i))
        ⟨i₀, Finset.mem_univ _, by simp [C, hi₀]⟩
    rw [h] at this
    exact IH _ this C rfl
  have D : Disjoint (piFinset B) (piFinset C) :=
    haveI : Disjoint (B i₀) (C i₀) := by simp [B, C]
    piFinset_disjoint_of_disjoint B C this
  have pi_BC : piFinset A = piFinset B union piFinset C := by
    apply Finset.Subset.antisymm
    · intro r hr
      by_cases hri₀ : r i₀ = j₂
      · apply Finset.mem_union_right
        refine mem_piFinset.2 fun i => ?_
        by_cases hi : i = i₀
        · have : r i₀ in C i₀ := by simp [C, hri₀]
          rwa [hi]
        · simp [C, hi, mem_piFinset.1 hr i]
      · apply Finset.mem_union_left
        refine mem_piFinset.2 fun i => ?_
        by_cases hi : i = i₀
        · have : r i₀ in B i₀ := by simp [B, hri₀, mem_piFinset.1 hr i₀]
          rwa [hi]
        · simp [B, hi, mem_piFinset.1 hr i]
    · exact
        Finset.union_subset (piFinset_subset _ _ fun i => B_subset_A i)
          (piFinset_subset _ _ fun i => C_subset_A i)
  rw [A_eq_BC]
  simp only [MultilinearMap.map_update_add, Beq, Ceq, Brec, Crec, pi_BC]
  rw [← Finset.sum_union D]

/--
theorem `map_sum_finset` / 定理 `map_sum_finset`

English:
theorem map_sum_finset
  given: [DecidableEq ι] [Fintype ι]
  proof: f.map_sum_finset_aux _ _ rfl

中文:
定理 map_sum_finset
  条件: [DecidableEq ι] [有限类型 ι]
  证明: f.map_sum_finset_aux _ _ rfl

Depends on / 依赖: f.map_sum_finset_aux, map_sum_finset_aux
-/
theorem map_sum_finset [DecidableEq ι] [Fintype ι] :
    (f fun i => ∑ j in A i, g i j) = ∑ r in piFinset A, f fun i => g i (r i) :=
  f.map_sum_finset_aux _ _ rfl

/--
theorem `map_sum` / 定理 `map_sum`

English:
theorem map_sum
  given: [DecidableEq ι] [Fintype ι] [forall i, Fintype (α i)]
  proof: f.map_sum_finset g fun _ => Finset.univ

中文:
定理 map_sum
  条件: [DecidableEq ι] [有限类型 ι] [对任意 i, 有限类型 (α i)]
  证明: f.map_sum_finset g fun _ => Finset.univ

Depends on / 依赖: Finset, Finset.univ, f.map_sum_finset, map_sum_finset
-/
theorem map_sum [DecidableEq ι] [Fintype ι] [forall i, Fintype (α i)] :
    (f fun i => ∑ j, g i j) = ∑ r : forall i, α i, f fun i => g i (r i) :=
  f.map_sum_finset g fun _ => Finset.univ

/--
theorem `map_update_sum` / 定理 `map_update_sum`

English:
theorem map_update_sum
  statement: {α : Type*} [DecidableEq ι] (t : Finset α) (i : ι) (g : α -> M₁ i)
  proof: by
  classical
    induction t using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, ih]

中文:
定理 map_update_sum
  结论: {α : 类型} [DecidableEq ι] (t : 有限集 α) (i : ι) (g : α -> M₁ i)
  证明: by
  classical
    induction t using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, ih]

Depends on / 依赖: Finset, Finset.induction, Finset.sum_insert, classical, insert, sum_insert
-/
theorem map_update_sum {α : Type*} [DecidableEq ι] (t : Finset α) (i : ι) (g : α -> M₁ i)
    (m : forall i, M₁ i) : f (update m i (∑ a in t, g a)) = ∑ a in t, f (update m i (g a)) := by
  classical
    induction t using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, ih]

end ApplySum

/-- Restrict the codomain of a multilinear map to a submodule.

This is the multilinear version of `LinearMap.codRestrict`. -/
@[simps]
/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂) (h : forall v, f v in p)
  body: ⟨f v, h v⟩
map_update_add' _ _ _ _ := Subtype.ext MultilinearMap.map_update_add _ _ _ _ _
map_update_smul' _ _ _ _ := Subtype.ext MultilinearMap.map_update_smul _ _ _ _ _

中文:
定义 codRestrict
  签名: (f : 多重线性映射 R M₁ M₂) (p : 子模 R M₂) (h : 对任意 v, f v in p)
  定义体: ⟨f v, h v⟩
map_update_add' _ _ _ _ := Subtype.ext MultilinearMap.map_update_add _ _ _ _ _
map_update_smul' _ _ _ _ := Subtype.ext MultilinearMap.map_update_smul _ _ _ _ _
-/
def codRestrict (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂) (h : forall v, f v in p) :
    MultilinearMap R M₁ p where
  toFun v := ⟨f v, h v⟩
map_update_add' _ _ _ _ := Subtype.ext MultilinearMap.map_update_add _ _ _ _ _
map_update_smul' _ _ _ _ := Subtype.ext MultilinearMap.map_update_smul _ _ _ _ _

section RestrictScalar

variable (R)
variable {A : Type*} [Semiring A] [SMul R A] [forall i : ι, Module A (M₁ i)] [Module A M₂]
  [forall i, IsScalarTower R A (M₁ i)] [IsScalarTower R A M₂]

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (f : MultilinearMap A M₁ M₂)
  body: f
  map_update_add' := f.map_update_add
  map_update_smul' m i := (f.toLinearMap m i).map_smul_of_tower

@[simp]

中文:
定义 restrictScalars
  签名: (f : 多重线性映射 A M₁ M₂)
  定义体: f
  map_update_add' := f.map_update_add
  map_update_smul' m i := (f.toLinearMap m i).map_smul_of_tower

@[simp]
-/
def restrictScalars (f : MultilinearMap A M₁ M₂) : MultilinearMap R M₁ M₂ where
  toFun := f
  map_update_add' := f.map_update_add
  map_update_smul' m i := (f.toLinearMap m i).map_smul_of_tower

@[simp]
/--
theorem `coe_restrictScalars` / 定理 `coe_restrictScalars`

English:
theorem coe_restrictScalars
  given: (f : MultilinearMap A M₁ M₂)
  statement: ⇑(f.restrictScalars R) = f
  proof: rfl

中文:
定理 coe_restrictScalars
  条件: (f : 多重线性映射 A M₁ M₂)
  结论: ⇑(f.restrictScalars R) = f
  证明: rfl
-/
theorem coe_restrictScalars (f : MultilinearMap A M₁ M₂) : ⇑(f.restrictScalars R) = f :=
  rfl

end RestrictScalar

section

variable {ι₁ ι₂ ι₃ : Type*}

/-- Transfer the arguments to a map along an equivalence between argument indices.

The naming is derived from `Finsupp.domCongr`, noting that here the permutation applies to the
domain of the domain. -/
@[simps apply]
/--
Definition of `domDomCongr` / `domDomCongr` 的定义

English:
definition domDomCongr
  signature: (σ : ι₁ ≃ ι₂) (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃)
  body: m fun i => v (σ i)
  map_update_add' v i a b := by
    let := σ.injective.decidableEq
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_update_add]
  map_update_smul' v i a b := by
    let := σ.injective.decidableEq
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_update

中文:
定义 domDomCongr
  签名: (σ : ι₁ ≃ ι₂) (m : 多重线性映射 R (fun _ : ι₁ => M₂) M₃)
  定义体: m fun i => v (σ i)
  map_update_add' v i a b := by
    let := σ.injective.decidableEq
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_update_add]
  map_update_smul' v i a b := by
    let := σ.injective.decidableEq
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_update
-/
def domDomCongr (σ : ι₁ ≃ ι₂) (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    MultilinearMap R (fun _ : ι₂ => M₂) M₃ where
  toFun v := m fun i => v (σ i)
  map_update_add' v i a b := by
    let := σ.injective.decidableEq
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_update_add]
  map_update_smul' v i a b := by
    let := σ.injective.decidableEq
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_update_smul]

/--
theorem `domDomCongr_trans` / 定理 `domDomCongr_trans`

English:
theorem domDomCongr_trans
  statement: (σ₁ : ι₁ ≃ ι₂) (σ₂ : ι₂ ≃ ι₃)
  proof: rfl

中文:
定理 domDomCongr_trans
  结论: (σ₁ : ι₁ ≃ ι₂) (σ₂ : ι₂ ≃ ι₃)
  证明: rfl
-/
theorem domDomCongr_trans (σ₁ : ι₁ ≃ ι₂) (σ₂ : ι₂ ≃ ι₃)
    (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    m.domDomCongr (σ₁.trans σ₂) = (m.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl

/--
theorem `domDomCongr_mul` / 定理 `domDomCongr_mul`

English:
theorem domDomCongr_mul
  statement: (σ₁ : Equiv.Perm ι₁) (σ₂ : Equiv.Perm ι₁)
  proof: rfl

中文:
定理 domDomCongr_mul
  结论: (σ₁ : 等价.置换 ι₁) (σ₂ : 等价.置换 ι₁)
  证明: rfl
-/
theorem domDomCongr_mul (σ₁ : Equiv.Perm ι₁) (σ₂ : Equiv.Perm ι₁)
    (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    m.domDomCongr (σ₂ * σ₁) = (m.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl

/-- `MultilinearMap.domDomCongr` as an equivalence.

This is declared separately because it does not work with dot notation. -/
@[simps apply symm_apply]
/--
Definition of `domDomCongrEquiv` / `domDomCongrEquiv` 的定义

English:
definition domDomCongrEquiv
  signature: (σ : ι₁ ≃ ι₂)
  body: domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv m := by
    ext
    simp [domDomCongr]
  right_inv m := by
    ext
    simp [domDomCongr]
  map_add' a b := by
    ext
    simp [domDomCongr]

中文:
定义 domDomCongrEquiv
  签名: (σ : ι₁ ≃ ι₂)
  定义体: domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv m := by
    ext
    simp [domDomCongr]
  right_inv m := by
    ext
    simp [domDomCongr]
  map_add' a b := by
    ext
    simp [domDomCongr]

Depends on / 依赖: domDomCongr
-/
def domDomCongrEquiv (σ : ι₁ ≃ ι₂) :
    MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃+ MultilinearMap R (fun _ : ι₂ => M₂) M₃ where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv m := by
    ext
    simp [domDomCongr]
  right_inv m := by
    ext
    simp [domDomCongr]
  map_add' a b := by
    ext
    simp [domDomCongr]

/-- The results of applying `domDomCongr` to two maps are equal if
and only if those maps are. -/
@[simp]
/--
theorem `domDomCongr_eq_iff` / 定理 `domDomCongr_eq_iff`

English:
theorem domDomCongr_eq_iff
  given: (σ : ι₁ ≃ ι₂) (f g : MultilinearMap R (fun _ : ι₁ => M₂) M₃)
  proof: (domDomCongrEquiv σ : _ ≃+ MultilinearMap R (fun _ => M₂) M₃).apply_eq_iff_eq

中文:
定理 domDomCongr_eq_iff
  条件: (σ : ι₁ ≃ ι₂) (f g : 多重线性映射 R (fun _ : ι₁ => M₂) M₃)
  证明: (domDomCongrEquiv σ : _ ≃+ MultilinearMap R (fun _ => M₂) M₃).apply_eq_iff_eq

Depends on / 依赖: MultilinearMap, apply_eq_iff_eq, domDomCongrEquiv
-/
theorem domDomCongr_eq_iff (σ : ι₁ ≃ ι₂) (f g : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    f.domDomCongr σ = g.domDomCongr σ ↔ f = g :=
  (domDomCongrEquiv σ : _ ≃+ MultilinearMap R (fun _ => M₂) M₃).apply_eq_iff_eq

end


/--
lemma `domDomRestrict_aux` / 引理 `domDomRestrict_aux`

English:
lemma domDomRestrict_aux
  statement: {ι} [DecidableEq ι] (P : ι -> Prop) [DecidablePred P] {M₁ : ι -> Type*}
  proof: by grind

中文:
引理 domDomRestrict_aux
  结论: {ι} [DecidableEq ι] (P : ι -> 命题) [DecidablePred P] {M₁ : ι -> 类型}
  证明: by grind
-/
lemma domDomRestrict_aux {ι} [DecidableEq ι] (P : ι -> Prop) [DecidablePred P] {M₁ : ι -> Type*}
    [DecidableEq {a // P a}]
    (x : (i : {a // P a}) -> M₁ i) (z : (i : {a // ¬ P a}) -> M₁ i) (i : {a : ι // P a})
    (c : M₁ i) : (fun j => if h : P j then Function.update x i c ⟨j, h⟩ else z ⟨j, h⟩) =
    Function.update (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) i c := by grind

/--
lemma `domDomRestrict_aux_right` / 引理 `domDomRestrict_aux_right`

English:
lemma domDomRestrict_aux_right
  statement: {ι} [DecidableEq ι] (P : ι -> Prop) [DecidablePred P] {M₁ : ι -> Type*}
  proof: by
  simpa only [dite_not] using domDomRestrict_aux _ z (fun j => x ⟨j.1, not_not.mp j.2⟩) i c

中文:
引理 domDomRestrict_aux_right
  结论: {ι} [DecidableEq ι] (P : ι -> 命题) [DecidablePred P] {M₁ : ι -> 类型}
  证明: by
  simpa only [dite_not] using domDomRestrict_aux _ z (fun j => x ⟨j.1, not_not.mp j.2⟩) i c

Depends on / 依赖: dite_not, domDomRestrict_aux, not_not, not_not.mp
-/
lemma domDomRestrict_aux_right {ι} [DecidableEq ι] (P : ι -> Prop) [DecidablePred P] {M₁ : ι -> Type*}
    [DecidableEq {a // ¬ P a}]
    (x : (i : {a // P a}) -> M₁ i) (z : (i : {a // ¬ P a}) -> M₁ i) (i : {a : ι // ¬ P a})
    (c : M₁ i) : (fun j => if h : P j then x ⟨j, h⟩ else Function.update z i c ⟨j, h⟩) =
    Function.update (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) i c := by
  simpa only [dite_not] using domDomRestrict_aux _ z (fun j => x ⟨j.1, not_not.mp j.2⟩) i c

/--
Definition of `domDomRestrict` / `domDomRestrict` 的定义

English:
definition domDomRestrict
  signature: (f : MultilinearMap R M₁ M₂) (P : ι -> Prop) [DecidablePred P]
  body: f (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩)
  map_update_add' x i a b := by
    classical
    repeat (rw [domDomRestrict_aux])
    simp only [MultilinearMap.map_update_add]
  map_update_smul' z i c a := by
    classical
    repeat (rw [domDomRestrict_aux])
    simp only [MultilinearMap.map_u

中文:
定义 domDomRestrict
  签名: (f : 多重线性映射 R M₁ M₂) (P : ι -> 命题) [DecidablePred P]
  定义体: f (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩)
  map_update_add' x i a b := by
    classical
    repeat (rw [domDomRestrict_aux])
    simp only [MultilinearMap.map_update_add]
  map_update_smul' z i c a := by
    classical
    repeat (rw [domDomRestrict_aux])
    simp only [MultilinearMap.map_u
-/
def domDomRestrict (f : MultilinearMap R M₁ M₂) (P : ι -> Prop) [DecidablePred P]
    (z : (i : {a : ι // ¬ P a}) -> M₁ i) :
    MultilinearMap R (fun (i : {a : ι // P a}) => M₁ i) M₂ where
  toFun x := f (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩)
  map_update_add' x i a b := by
    classical
    repeat (rw [domDomRestrict_aux])
    simp only [MultilinearMap.map_update_add]
  map_update_smul' z i c a := by
    classical
    repeat (rw [domDomRestrict_aux])
    simp only [MultilinearMap.map_update_smul]

@[simp]
/--
lemma `domDomRestrict_apply` / 引理 `domDomRestrict_apply`

English:
lemma domDomRestrict_apply
  statement: (f : MultilinearMap R M₁ M₂) (P : ι -> Prop)
  proof: rfl

中文:
引理 domDomRestrict_apply
  结论: (f : 多重线性映射 R M₁ M₂) (P : ι -> 命题)
  证明: rfl
-/
lemma domDomRestrict_apply (f : MultilinearMap R M₁ M₂) (P : ι -> Prop)
    [DecidablePred P] (x : (i : {a // P a}) -> M₁ i) (z : (i : {a // ¬ P a}) -> M₁ i) :
    f.domDomRestrict P z x = f (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) := rfl

-- TODO: Should add a ref here when available.
/--
Definition of `linearDeriv` / `linearDeriv` 的定义

English:
definition linearDeriv
  signature: [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
  body: ∑ i : ι, (f.toLinearMap x i).comp (LinearMap.proj i)

@[simp]

中文:
定义 linearDeriv
  签名: [DecidableEq ι] [有限类型 ι] (f : 多重线性映射 R M₁ M₂)
  定义体: ∑ i : ι, (f.toLinearMap x i).comp (LinearMap.proj i)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.proj, f.toLinearMap, toLinearMap
-/
def linearDeriv [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
    (x : (i : ι) -> M₁ i) : ((i : ι) -> M₁ i) ->ₗ[R] M₂ :=
  ∑ i : ι, (f.toLinearMap x i).comp (LinearMap.proj i)

@[simp]
/--
lemma `linearDeriv_apply` / 引理 `linearDeriv_apply`

English:
lemma linearDeriv_apply
  statement: [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
  proof: by
  unfold linearDeriv
  simp only [LinearMap.coe_sum, LinearMap.coe_comp, LinearMap.coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, toLinearMap_apply]

中文:
引理 linearDeriv_apply
  结论: [DecidableEq ι] [有限类型 ι] (f : 多重线性映射 R M₁ M₂)
  证明: by
  unfold linearDeriv
  simp only [LinearMap.coe_sum, LinearMap.coe_comp, LinearMap.coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, toLinearMap_apply]

Depends on / 依赖: Finset, Finset.sum_apply, Function, Function.comp_apply, Function.eval, LinearMap, LinearMap.coe_comp, LinearMap.coe_proj, LinearMap.coe_sum, coe_comp, coe_proj, coe_sum, comp_apply, linearDeriv, sum_apply, toLinearMap_apply
-/
lemma linearDeriv_apply [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
    (x y : (i : ι) -> M₁ i) :
    f.linearDeriv x y = ∑ i, f (update x i (y i)) := by
  unfold linearDeriv
  simp only [LinearMap.coe_sum, LinearMap.coe_comp, LinearMap.coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, toLinearMap_apply]

end Semiring

end MultilinearMap

namespace LinearMap

variable [Semiring R]
variable [forall i, AddCommMonoid (M₁ i)] [forall i, AddCommMonoid (M₁' i)]
  [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄] [AddCommMonoid M']
variable [forall i, Module R (M₁ i)] [forall i, Module R (M₁' i)]
  [Module R M₂] [Module R M₃] [Module R M₄] [Module R M']

/--
Definition of `compMultilinearMap` / `compMultilinearMap` 的定义

English:
definition compMultilinearMap
  signature: (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂)
  body: g ∘ f
  map_update_add' m i x y := by simp
  map_update_smul' m i c x := by simp

@[simp]

中文:
定义 compMultilinearMap
  签名: (g : M₂ ->ₗ[R] M₃) (f : 多重线性映射 R M₁ M₂)
  定义体: g ∘ f
  map_update_add' m i x y := by simp
  map_update_smul' m i c x := by simp

@[simp]
-/
def compMultilinearMap (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) : MultilinearMap R M₁ M₃ where
  toFun := g ∘ f
  map_update_add' m i x y := by simp
  map_update_smul' m i c x := by simp

@[simp]
/--
theorem `coe_compMultilinearMap` / 定理 `coe_compMultilinearMap`

English:
theorem coe_compMultilinearMap
  given: (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂)
  proof: rfl

@[simp]

中文:
定理 coe_compMultilinearMap
  条件: (g : M₂ ->ₗ[R] M₃) (f : 多重线性映射 R M₁ M₂)
  证明: rfl

@[simp]
-/
theorem coe_compMultilinearMap (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) :
    ⇑(g.compMultilinearMap f) = g ∘ f :=
  rfl

@[simp]
/--
theorem `compMultilinearMap_apply` / 定理 `compMultilinearMap_apply`

English:
theorem compMultilinearMap_apply
  given: (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) (m : forall i, M₁ i)
  proof: rfl

@[simp]

中文:
定理 compMultilinearMap_apply
  条件: (g : M₂ ->ₗ[R] M₃) (f : 多重线性映射 R M₁ M₂) (m : 对任意 i, M₁ i)
  证明: rfl

@[simp]
-/
theorem compMultilinearMap_apply (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) (m : forall i, M₁ i) :
    g.compMultilinearMap f m = g (f m) :=
  rfl

@[simp]
/--
theorem `id_compMultilinearMap` / 定理 `id_compMultilinearMap`

English:
theorem id_compMultilinearMap
  given: (f : MultilinearMap R M₁ M₂)
  proof: rfl

中文:
定理 id_compMultilinearMap
  条件: (f : 多重线性映射 R M₁ M₂)
  证明: rfl
-/
theorem id_compMultilinearMap (f : MultilinearMap R M₁ M₂) :
    (id : M₂ ->ₗ[R] M₂).compMultilinearMap f = f := rfl

/--
theorem `comp_compMultilinearMap` / 定理 `comp_compMultilinearMap`

English:
theorem comp_compMultilinearMap
  given: (g : M₃ ->ₗ[R] M₄) (g' : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂)
  proof: rfl

中文:
定理 comp_compMultilinearMap
  条件: (g : M₃ ->ₗ[R] M₄) (g' : M₂ ->ₗ[R] M₃) (f : 多重线性映射 R M₁ M₂)
  证明: rfl
-/
theorem comp_compMultilinearMap (g : M₃ ->ₗ[R] M₄) (g' : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) :
    (g.comp g').compMultilinearMap f = g.compMultilinearMap (g'.compMultilinearMap f) := rfl

/--
theorem `compMultilinearMap_compLinearMap` / 定理 `compMultilinearMap_compLinearMap`

English:
theorem compMultilinearMap_compLinearMap
  proof: rfl

@[simp]

中文:
定理 compMultilinearMap_compLinearMap
  证明: rfl

@[simp]
-/
theorem compMultilinearMap_compLinearMap
    (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) (f' : forall i, M₁' i ->ₗ[R] M₁ i) :
    g.compMultilinearMap (f.compLinearMap f') = (g.compMultilinearMap f).compLinearMap f' := rfl

@[simp]
/--
theorem `compMultilinearMap_zero` / 定理 `compMultilinearMap_zero`

English:
theorem compMultilinearMap_zero
  given: (g : M₂ ->ₗ[R] M₃)
  proof: MultilinearMap.ext fun _ => map_zero g

@[simp]

中文:
定理 compMultilinearMap_zero
  条件: (g : M₂ ->ₗ[R] M₃)
  证明: MultilinearMap.ext fun _ => map_zero g

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.ext, map_zero
-/
theorem compMultilinearMap_zero (g : M₂ ->ₗ[R] M₃) :
    g.compMultilinearMap (0 : MultilinearMap R M₁ M₂) = 0 :=
  MultilinearMap.ext fun _ => map_zero g

@[simp]
/--
theorem `zero_compMultilinearMap` / 定理 `zero_compMultilinearMap`

English:
theorem zero_compMultilinearMap
  given: (f : MultilinearMap R M₁ M₂)
  proof: rfl

@[simp]

中文:
定理 zero_compMultilinearMap
  条件: (f : 多重线性映射 R M₁ M₂)
  证明: rfl

@[simp]
-/
theorem zero_compMultilinearMap (f : MultilinearMap R M₁ M₂) :
    (0 : M₂ ->ₗ[R] M₃).compMultilinearMap f = 0 := rfl

@[simp]
/--
theorem `compMultilinearMap_add` / 定理 `compMultilinearMap_add`

English:
theorem compMultilinearMap_add
  given: (g : M₂ ->ₗ[R] M₃) (f₁ f₂ : MultilinearMap R M₁ M₂)
  proof: MultilinearMap.ext fun _ => map_add g _ _

@[simp]

中文:
定理 compMultilinearMap_add
  条件: (g : M₂ ->ₗ[R] M₃) (f₁ f₂ : 多重线性映射 R M₁ M₂)
  证明: MultilinearMap.ext fun _ => map_add g _ _

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.ext, map_add
-/
theorem compMultilinearMap_add (g : M₂ ->ₗ[R] M₃) (f₁ f₂ : MultilinearMap R M₁ M₂) :
    g.compMultilinearMap (f₁ + f₂) = g.compMultilinearMap f₁ + g.compMultilinearMap f₂ :=
  MultilinearMap.ext fun _ => map_add g _ _

@[simp]
/--
theorem `add_compMultilinearMap` / 定理 `add_compMultilinearMap`

English:
theorem add_compMultilinearMap
  given: (g₁ g₂ : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂)
  proof: rfl

@[simp]

中文:
定理 add_compMultilinearMap
  条件: (g₁ g₂ : M₂ ->ₗ[R] M₃) (f : 多重线性映射 R M₁ M₂)
  证明: rfl

@[simp]
-/
theorem add_compMultilinearMap (g₁ g₂ : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) :
    (g₁ + g₂).compMultilinearMap f = g₁.compMultilinearMap f + g₂.compMultilinearMap f := rfl

@[simp]
/--
theorem `compMultilinearMap_smul` / 定理 `compMultilinearMap_smul`

English:
theorem compMultilinearMap_smul
  statement: [DistribSMul S M₂] [DistribSMul S M₃]
  proof: MultilinearMap.ext fun _ => g.map_smul_of_tower _ _

@[simp]

中文:
定理 compMultilinearMap_smul
  结论: [分配标量乘法 S M₂] [分配标量乘法 S M₃]
  证明: MultilinearMap.ext fun _ => g.map_smul_of_tower _ _

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.ext, g.map_smul_of_tower, map_smul_of_tower
-/
theorem compMultilinearMap_smul [DistribSMul S M₂] [DistribSMul S M₃]
    [SMulCommClass R S M₂] [SMulCommClass R S M₃] [CompatibleSMul M₂ M₃ S R]
    (g : M₂ ->ₗ[R] M₃) (s : S) (f : MultilinearMap R M₁ M₂) :
    g.compMultilinearMap (s • f) = s • g.compMultilinearMap f :=
  MultilinearMap.ext fun _ => g.map_smul_of_tower _ _

@[simp]
/--
theorem `smul_compMultilinearMap` / 定理 `smul_compMultilinearMap`

English:
theorem smul_compMultilinearMap
  statement: [Monoid S] [DistribMulAction S M₃] [SMulCommClass R S M₃]
  proof: rfl

中文:
定理 smul_compMultilinearMap
  结论: [幺半群 S] [分配乘法作用 S M₃] [标量交换类 R S M₃]
  证明: rfl
-/
theorem smul_compMultilinearMap [Monoid S] [DistribMulAction S M₃] [SMulCommClass R S M₃]
    (g : M₂ ->ₗ[R] M₃) (s : S) (f : MultilinearMap R M₁ M₂) :
    (s • g).compMultilinearMap f = s • g.compMultilinearMap f := rfl

/-- The multilinear version of `LinearMap.subtype_comp_codRestrict` -/
@[simp]
/--
theorem `subtype_compMultilinearMap_codRestrict` / 定理 `subtype_compMultilinearMap_codRestrict`

English:
theorem subtype_compMultilinearMap_codRestrict
  statement: (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂)
  proof: rfl

中文:
定理 subtype_compMultilinearMap_codRestrict
  结论: (f : 多重线性映射 R M₁ M₂) (p : 子模 R M₂)
  证明: rfl
-/
theorem subtype_compMultilinearMap_codRestrict (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂)
    (h) : p.subtype.compMultilinearMap (f.codRestrict p h) = f :=
  rfl

/-- The multilinear version of `LinearMap.comp_codRestrict` -/
@[simp]
/--
theorem `compMultilinearMap_codRestrict` / 定理 `compMultilinearMap_codRestrict`

English:
theorem compMultilinearMap_codRestrict
  statement: (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂)
  proof: rfl

中文:
定理 compMultilinearMap_codRestrict
  结论: (g : M₂ ->ₗ[R] M₃) (f : 多重线性映射 R M₁ M₂)
  证明: rfl
-/
theorem compMultilinearMap_codRestrict (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂)
    (p : Submodule R M₃) (h) :
    (g.codRestrict p h).compMultilinearMap f =
      (g.compMultilinearMap f).codRestrict p fun v => h (f v) :=
  rfl

variable {ι₁ ι₂ : Type*}

@[simp]
/--
theorem `compMultilinearMap_domDomCongr` / 定理 `compMultilinearMap_domDomCongr`

English:
theorem compMultilinearMap_domDomCongr
  statement: (σ : ι₁ ≃ ι₂) (g : M₂ ->ₗ[R] M₃)
  proof: by
  ext
  simp [MultilinearMap.domDomCongr]

中文:
定理 compMultilinearMap_domDomCongr
  结论: (σ : ι₁ ≃ ι₂) (g : M₂ ->ₗ[R] M₃)
  证明: by
  ext
  simp [MultilinearMap.domDomCongr]

Depends on / 依赖: MultilinearMap, MultilinearMap.domDomCongr, domDomCongr
-/
theorem compMultilinearMap_domDomCongr (σ : ι₁ ≃ ι₂) (g : M₂ ->ₗ[R] M₃)
    (f : MultilinearMap R (fun _ : ι₁ => M') M₂) :
    (g.compMultilinearMap f).domDomCongr σ = g.compMultilinearMap (f.domDomCongr σ) := by
  ext
  simp [MultilinearMap.domDomCongr]

end LinearMap

namespace MultilinearMap

section Semiring

variable [Semiring R] [(i : ι) -> AddCommMonoid (M₁ i)] [(i : ι) -> Module R (M₁ i)]
  [AddCommMonoid M₂] [Module R M₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: S] [DistribMulAction S M₂] [SMulCommClass R S M₂] :
  body: fast_instance% FunLike.distribMulAction

中文:
实例 [幺半群
  签名: S] [分配乘法作用 S M₂] [标量交换类 R S M₂] :
  定义体: fast_instance% FunLike.distribMulAction

Depends on / 依赖: FunLike, FunLike.distribMulAction, distribMulAction, fast_instance
-/
instance [Monoid S] [DistribMulAction S M₂] [SMulCommClass R S M₂] :
    DistribMulAction S (MultilinearMap R M₁ M₂) := fast_instance% FunLike.distribMulAction

section Module

variable [Semiring S] [Module S M₂] [SMulCommClass R S M₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module S (MultilinearMap R M₁ M₂)
  body: fast_instance%
  FunLike.module

中文:
实例 :
  签名: 模 S (多重线性映射 R M₁ M₂)
  定义体: fast_instance%
  FunLike.module

Depends on / 依赖: fast_instance
-/
instance : Module S (MultilinearMap R M₁ M₂) := fast_instance%
  FunLike.module

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.IsTorsionFree
  signature: S M₂] : Module.IsTorsionFree S (MultilinearMap R M₁ M₂)
  body: coe_injective.moduleIsTorsionFree _ FunLike.coe_smul

中文:
实例 [模.是无挠
  签名: S M₂] : 模.是无挠 S (多重线性映射 R M₁ M₂)
  定义体: coe_injective.moduleIsTorsionFree _ FunLike.coe_smul

Depends on / 依赖: FunLike, FunLike.coe_smul, coe_injective, coe_injective.moduleIsTorsionFree, coe_smul, moduleIsTorsionFree
-/
instance [Module.IsTorsionFree S M₂] : Module.IsTorsionFree S (MultilinearMap R M₁ M₂) :=
  coe_injective.moduleIsTorsionFree _ FunLike.coe_smul

variable [AddCommMonoid M₃] [Module S M₃] [Module R M₃] [SMulCommClass R S M₃]

variable (S) in
/-- `LinearMap.compMultilinearMap` as an `S`-linear map. -/
@[simps]
/--
Definition of `_root_.LinearMap.compMultilinearMapₗ` / `_root_.LinearMap.compMultilinearMapₗ` 的定义

English:
definition _root_.LinearMap.compMultilinearMapₗ
  signature: [LinearMap.CompatibleSMul M₂ M₃ S R] (g : M₂ ->ₗ[R] M₃)
  body: g.compMultilinearMap
  map_add' := g.compMultilinearMap_add
  map_smul' := g.compMultilinearMap_smul

中文:
定义 _root_.线性映射.compMultilinearMapₗ
  签名: [线性映射.余mpatibleSMul M₂ M₃ S R] (g : M₂ ->ₗ[R] M₃)
  定义体: g.compMultilinearMap
  map_add' := g.compMultilinearMap_add
  map_smul' := g.compMultilinearMap_smul

Depends on / 依赖: compMultilinearMap, g.compMultilinearMap
-/
def _root_.LinearMap.compMultilinearMapₗ [LinearMap.CompatibleSMul M₂ M₃ S R] (g : M₂ ->ₗ[R] M₃) :
    MultilinearMap R M₁ M₂ ->ₗ[S] MultilinearMap R M₁ M₃ where
  toFun := g.compMultilinearMap
  map_add' := g.compMultilinearMap_add
  map_smul' := g.compMultilinearMap_smul

variable (S) in
/-- An isomorphism of multilinear maps given an isomorphism between their codomains.

This is `LinearMap.compMultilinearMap` as an `S`-linear equivalence,
and the multilinear version of `LinearEquiv.congrRight`. -/
@[simps! apply symm_apply]
/--
Definition of `_root_.LinearEquiv.multilinearMapCongrRight` / `_root_.LinearEquiv.multilinearMapCongrRight` 的定义

English:
definition _root_.LinearEquiv.multilinearMapCongrRight
  body: g.toLinearMap.compMultilinearMapₗ S
  invFun := g.symm.toLinearMap.compMultilinearMapₗ S
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

中文:
定义 _root_.线性等价.multilinearMapCongrRight
  定义体: g.toLinearMap.compMultilinearMapₗ S
  invFun := g.symm.toLinearMap.compMultilinearMapₗ S
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

Depends on / 依赖: g.toLinearMap.compMultilinearMap, toLinearMap
-/
def _root_.LinearEquiv.multilinearMapCongrRight
    [LinearMap.CompatibleSMul M₂ M₃ S R] [LinearMap.CompatibleSMul M₃ M₂ S R] (g : M₂ ≃ₗ[R] M₃) :
    MultilinearMap R M₁ M₂ ≃ₗ[S] MultilinearMap R M₁ M₃ where
  __ := g.toLinearMap.compMultilinearMapₗ S
  invFun := g.symm.toLinearMap.compMultilinearMapₗ S
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

variable (R S M₁ M₂ M₃)

section OfSubsingleton

/-- Linear equivalence between linear maps `M₂ →ₗ[R] M₃`
and one-multilinear maps `MultilinearMap R (fun _ : ι ↦ M₂) M₃`. -/
@[simps +simpRhs]
/--
Definition of `ofSubsingletonₗ` / `ofSubsingletonₗ` 的定义

English:
definition ofSubsingletonₗ
  signature: [Subsingleton ι] (i : ι)
  body: { ofSubsingleton R M₂ M₃ i with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

中文:
定义 ofSubsingletonₗ
  签名: [子单例 ι] (i : ι)
  定义体: { ofSubsingleton R M₂ M₃ i with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

Depends on / 依赖: map_add, map_smul, ofSubsingleton
-/
def ofSubsingletonₗ [Subsingleton ι] (i : ι) :
    (M₂ ->ₗ[R] M₃) ≃ₗ[S] MultilinearMap R (fun _ : ι => M₂) M₃ :=
  { ofSubsingleton R M₂ M₃ i with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

end OfSubsingleton

/-- The dependent version of `MultilinearMap.domDomCongrLinearEquiv`. -/
@[simps apply symm_apply]
/--
Definition of `domDomCongrLinearEquiv'` / `domDomCongrLinearEquiv'` 的定义

English:
definition domDomCongrLinearEquiv'
  signature: {ι' : Type*} (σ : ι ≃ ι')
  body: { toFun := f ∘ (σ.piCongrLeft' M₁).symm
      map_update_add' := fun m i => by
        let := σ.decidableEq
        rw [← σ.apply_symm_apply i]
        intro x y
        simp only [comp_apply, piCongrLeft'_symm_update, f.map_update_add]
      map_update_smul' := fun m i c => by
        let := σ.deci

中文:
定义 domDomCongrLinearEquiv'
  签名: {ι' : 类型} (σ : ι ≃ ι')
  定义体: { toFun := f ∘ (σ.piCongrLeft' M₁).symm
      map_update_add' := fun m i => by
        let := σ.decidableEq
        rw [← σ.apply_symm_apply i]
        intro x y
        simp only [comp_apply, piCongrLeft'_symm_update, f.map_update_add]
      map_update_smul' := fun m i c => by
        let := σ.deci

Depends on / 依赖: Function, Function.comp, _symm_update, apply_symm_apply, comp_apply, decidableEq, f.map_update_add, f.map_update_smul, invFun, map_update_add, map_update_smul, piCongrLeft, symm.decidableEq, symm_apply_apply
-/
def domDomCongrLinearEquiv' {ι' : Type*} (σ : ι ≃ ι') :
    MultilinearMap R M₁ M₂ ≃ₗ[S] MultilinearMap R (fun i => M₁ (σ.symm i)) M₂ where
  toFun f :=
    { toFun := f ∘ (σ.piCongrLeft' M₁).symm
      map_update_add' := fun m i => by
        let := σ.decidableEq
        rw [← σ.apply_symm_apply i]
        intro x y
        simp only [comp_apply, piCongrLeft'_symm_update, f.map_update_add]
      map_update_smul' := fun m i c => by
        let := σ.decidableEq
        rw [← σ.apply_symm_apply i]
        intro x
        simp only [Function.comp, piCongrLeft'_symm_update, f.map_update_smul] }
  invFun f :=
    { toFun := f ∘ σ.piCongrLeft' M₁
      map_update_add' := fun m i => by
        let := σ.symm.decidableEq
        rw [← σ.symm_apply_apply i]
        intro x y
        simp only [comp_apply, piCongrLeft'_update, f.map_update_add]
      map_update_smul' := fun m i c => by
        let := σ.symm.decidableEq
        rw [← σ.symm_apply_apply i]
        intro x
        simp only [Function.comp, piCongrLeft'_update, f.map_update_smul] }
  map_add' f₁ f₂ := by
    ext
    simp only [Function.comp, coe_mk, add_apply]
  map_smul' c f := by
    ext
    simp only [Function.comp, coe_mk, smul_apply, RingHom.id_apply]
  left_inv f := by
    ext
    simp only [coe_mk, comp_apply, Equiv.symm_apply_apply]
  right_inv f := by
    ext
    simp only [coe_mk, comp_apply, Equiv.apply_symm_apply]

/-- The space of constant maps is equivalent to the space of maps that are multilinear with respect
to an empty family. -/
@[simps]
/--
Definition of `constLinearEquivOfIsEmpty` / `constLinearEquivOfIsEmpty` 的定义

English:
definition constLinearEquivOfIsEmpty
  signature: [IsEmpty ι]
  body: MultilinearMap.constOfIsEmpty R _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f 0
right_inv f := ext fun _ => MultilinearMap.congr_arg f Subsingleton.elim _ _

中文:
定义 constLinearEquivOfIsEmpty
  签名: [是空 ι]
  定义体: MultilinearMap.constOfIsEmpty R _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f 0
right_inv f := ext fun _ => MultilinearMap.congr_arg f Subsingleton.elim _ _

Depends on / 依赖: MultilinearMap, MultilinearMap.constOfIsEmpty, constOfIsEmpty
-/
def constLinearEquivOfIsEmpty [IsEmpty ι] : M₂ ≃ₗ[S] MultilinearMap R M₁ M₂ where
  toFun := MultilinearMap.constOfIsEmpty R _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f 0
right_inv f := ext fun _ => MultilinearMap.congr_arg f Subsingleton.elim _ _

/-- `MultilinearMap.domDomCongr` as a `LinearEquiv`. -/
@[simps apply symm_apply]
/--
Definition of `domDomCongrLinearEquiv` / `domDomCongrLinearEquiv` 的定义

English:
definition domDomCongrLinearEquiv
  signature: {ι₁ ι₂} (σ : ι₁ ≃ ι₂)
  body: { (domDomCongrEquiv σ :
      MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃+ MultilinearMap R (fun _ : ι₂ => M₂) M₃) with
    map_smul' := fun c f => by
      ext
      simp [MultilinearMap.domDomCongr] }

中文:
定义 domDomCongrLinearEquiv
  签名: {ι₁ ι₂} (σ : ι₁ ≃ ι₂)
  定义体: { (domDomCongrEquiv σ :
      MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃+ MultilinearMap R (fun _ : ι₂ => M₂) M₃) with
    map_smul' := fun c f => by
      ext
      simp [MultilinearMap.domDomCongr] }

Depends on / 依赖: MultilinearMap, MultilinearMap.domDomCongr, domDomCongr, domDomCongrEquiv, map_smul
-/
def domDomCongrLinearEquiv {ι₁ ι₂} (σ : ι₁ ≃ ι₂) :
    MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃ₗ[S] MultilinearMap R (fun _ : ι₂ => M₂) M₃ :=
  { (domDomCongrEquiv σ :
      MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃+ MultilinearMap R (fun _ : ι₂ => M₂) M₃) with
    map_smul' := fun c f => by
      ext
      simp [MultilinearMap.domDomCongr] }

end Module

end Semiring

section CommSemiring

variable [CommSemiring R] [forall i, AddCommMonoid (M₁ i)] [forall i, AddCommMonoid (M i)] [AddCommMonoid M₂]
  [forall i, Module R (M i)] [forall i, Module R (M₁ i)] [Module R M₂] (f f' : MultilinearMap R M₁ M₂)

section
variable [Π i, AddCommMonoid (M₁' i)] [Π i, Module R (M₁' i)]

/--
Definition of `domDomRestrictₗ` / `domDomRestrictₗ` 的定义

English:
definition domDomRestrictₗ
  signature: (f : MultilinearMap R M₁ M₂) (P : ι -> Prop) [DecidablePred P]
  body: fun z => domDomRestrict f P z
  map_update_add' := by
    intro h m i x y
    classical
    ext v
    simp [domDomRestrict_aux_right]
  map_update_smul' := by
    intro h m i c x
    classical
    ext v
    simp [domDomRestrict_aux_right]

中文:
定义 domDomRestrictₗ
  签名: (f : 多重线性映射 R M₁ M₂) (P : ι -> 命题) [DecidablePred P]
  定义体: fun z => domDomRestrict f P z
  map_update_add' := by
    intro h m i x y
    classical
    ext v
    simp [domDomRestrict_aux_right]
  map_update_smul' := by
    intro h m i c x
    classical
    ext v
    simp [domDomRestrict_aux_right]

Depends on / 依赖: domDomRestrict
-/
def domDomRestrictₗ (f : MultilinearMap R M₁ M₂) (P : ι -> Prop) [DecidablePred P] :
    MultilinearMap R (fun (i : {a : ι // ¬ P a}) => M₁ i)
      (MultilinearMap R (fun (i : {a : ι // P a}) => M₁ i) M₂) where
  toFun := fun z => domDomRestrict f P z
  map_update_add' := by
    intro h m i x y
    classical
    ext v
    simp [domDomRestrict_aux_right]
  map_update_smul' := by
    intro h m i c x
    classical
    ext v
    simp [domDomRestrict_aux_right]

/--
lemma `iteratedFDeriv_aux` / 引理 `iteratedFDeriv_aux`

English:
lemma iteratedFDeriv_aux
  statement: {ι} {M₁ : ι -> Type*} {α : Type*} [DecidableEq α]
  proof: by
  ext i
  rcases eq_or_ne a (e.symm i) with rfl | hne
  · rw [Equiv.apply_symm_apply e i, update_self, update_self]
  · rw [update_of_ne hne.symm, update_of_ne fun h => (Equiv.symm_apply_apply .. ▸ h ▸ hne) rfl]

中文:
引理 iteratedFDeriv_aux
  结论: {ι} {M₁ : ι -> 类型} {α : 类型} [DecidableEq α]
  证明: by
  ext i
  rcases eq_or_ne a (e.symm i) with rfl | hne
  · rw [Equiv.apply_symm_apply e i, update_self, update_self]
  · rw [update_of_ne hne.symm, update_of_ne fun h => (Equiv.symm_apply_apply .. ▸ h ▸ hne) rfl]

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.symm_apply_apply, apply_symm_apply, e.symm, eq_or_ne, hne.symm, symm_apply_apply, update_of_ne, update_self
-/
lemma iteratedFDeriv_aux {ι} {M₁ : ι -> Type*} {α : Type*} [DecidableEq α]
    (s : Set ι) [DecidableEq { x // x in s }] (e : α ≃ s)
    (m : α -> ((i : ι) -> M₁ i)) (a : α) (z : (i : ι) -> M₁ i) :
    (fun i => update m a z (e.symm i) i) =
      (fun i => update (fun j => m (e.symm j) j) (e a) (z (e a)) i) := by
  ext i
  rcases eq_or_ne a (e.symm i) with rfl | hne
  · rw [Equiv.apply_symm_apply e i, update_self, update_self]
  · rw [update_of_ne hne.symm, update_of_ne fun h => (Equiv.symm_apply_apply .. ▸ h ▸ hne) rfl]

/--
Definition of `iteratedFDerivComponent` / `iteratedFDerivComponent` 的定义

English:
definition iteratedFDerivComponent
  signature: {α : Type*}
  body: fun z =>
    { toFun := fun v => domDomRestrictₗ f (fun i => i in s) z (fun i => v (e.symm i) i)
      map_update_add' := by classical simp [iteratedFDeriv_aux]
      map_update_smul' := by classical simp [iteratedFDeriv_aux] }
  map_update_add' := by intros; ext; simp
  map_update_smul' := by intro

中文:
定义 iteratedFDerivComponent
  签名: {α : 类型}
  定义体: fun z =>
    { toFun := fun v => domDomRestrictₗ f (fun i => i in s) z (fun i => v (e.symm i) i)
      map_update_add' := by classical simp [iteratedFDeriv_aux]
      map_update_smul' := by classical simp [iteratedFDeriv_aux] }
  map_update_add' := by intros; ext; simp
  map_update_smul' := by intro
-/
noncomputable def iteratedFDerivComponent {α : Type*}
    (f : MultilinearMap R M₁ M₂) {s : Set ι} (e : α ≃ s) [DecidablePred (· in s)] :
    MultilinearMap R (fun (i : {a : ι // a ∉ s}) => M₁ i)
      (MultilinearMap R (fun (_ : α) => (forall i, M₁ i)) M₂) where
  toFun := fun z =>
    { toFun := fun v => domDomRestrictₗ f (fun i => i in s) z (fun i => v (e.symm i) i)
      map_update_add' := by classical simp [iteratedFDeriv_aux]
      map_update_smul' := by classical simp [iteratedFDeriv_aux] }
  map_update_add' := by intros; ext; simp
  map_update_smul' := by intros; ext; simp

open scoped Classical in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def iteratedFDeriv [Fintype ι]
  body: ∑ e : Fin k ↪ ι, iteratedFDerivComponent f e.toEquivRange (fun i => x i)

中文:
定义 noncomputable
  签名: def iteratedFDeriv [有限类型 ι]
  定义体: ∑ e : Fin k ↪ ι, iteratedFDerivComponent f e.toEquivRange (fun i => x i)
-/
protected noncomputable def iteratedFDeriv [Fintype ι]
    (f : MultilinearMap R M₁ M₂) (k : Nat) (x : (i : ι) -> M₁ i) :
    MultilinearMap R (fun (_ : Fin k) => (forall i, M₁ i)) M₂ :=
  ∑ e : Fin k ↪ ι, iteratedFDerivComponent f e.toEquivRange (fun i => x i)

/--
Definition of `compLinearMapₗ` / `compLinearMapₗ` 的定义

English:
definition compLinearMapₗ
  signature: (f : Π (i : ι), M₁ i ->ₗ[R] M₁' i)
  body: fun g => g.compLinearMap f
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

中文:
定义 compLinearMapₗ
  签名: (f : Π (i : ι), M₁ i ->ₗ[R] M₁' i)
  定义体: fun g => g.compLinearMap f
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
-/
@[simps] def compLinearMapₗ (f : Π (i : ι), M₁ i ->ₗ[R] M₁' i) :
    (MultilinearMap R M₁' M₂) ->ₗ[R] MultilinearMap R M₁ M₂ where
  toFun := fun g => g.compLinearMap f
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- An isomorphism of multilinear maps given an isomorphism between their domains.

This is `MultilinearMap.compLinearMap` as a linear equivalence,
and the multilinear version of `LinearEquiv.congrLeft`. -/
@[simps! apply symm_apply]
/--
Definition of `_root_.LinearEquiv.multilinearMapCongrLeft` / `_root_.LinearEquiv.multilinearMapCongrLeft` 的定义

English:
definition _root_.LinearEquiv.multilinearMapCongrLeft
  signature: (e : Π (i : ι), M₁ i ≃ₗ[R] M₁' i)
  body: compLinearMapₗ (e · |>.toLinearMap)
  invFun := compLinearMapₗ (e · |>.symm.toLinearMap)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

中文:
定义 _root_.线性等价.multilinearMapCongrLeft
  签名: (e : Π (i : ι), M₁ i ≃ₗ[R] M₁' i)
  定义体: compLinearMapₗ (e · |>.toLinearMap)
  invFun := compLinearMapₗ (e · |>.symm.toLinearMap)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

Depends on / 依赖: toLinearMap
-/
def _root_.LinearEquiv.multilinearMapCongrLeft (e : Π (i : ι), M₁ i ≃ₗ[R] M₁' i) :
    (MultilinearMap R M₁' M₂) ≃ₗ[R] MultilinearMap R M₁ M₂ where
  __ := compLinearMapₗ (e · |>.toLinearMap)
  invFun := compLinearMapₗ (e · |>.symm.toLinearMap)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/--
Definition of `compLinearMapMultilinear` / `compLinearMapMultilinear` 的定义

English:
definition compLinearMapMultilinear
  signature: :
  body: MultilinearMap.compLinearMapₗ
  map_update_add' := by
    intro _ f i f₁ f₂
    ext g x
    change (g fun j => update f i (f₁ + f₂) j <| x j) =
        (g fun j => update f i f₁ j <| x j) + g fun j => update f i f₂ j (x j)
    let c : Π (i : ι), (M₁ i ->ₗ[R] M₁' i) -> M₁' i := fun i f => f (x i)
   

中文:
定义 compLinearMapMultilinear
  签名: :
  定义体: MultilinearMap.compLinearMapₗ
  map_update_add' := by
    intro _ f i f₁ f₂
    ext g x
    change (g fun j => update f i (f₁ + f₂) j <| x j) =
        (g fun j => update f i f₁ j <| x j) + g fun j => update f i f₂ j (x j)
    let c : Π (i : ι), (M₁ i ->ₗ[R] M₁' i) -> M₁' i := fun i f => f (x i)
   
-/
@[simps] def compLinearMapMultilinear :
    @MultilinearMap R ι (fun i => M₁ i ->ₗ[R] M₁' i)
      ((MultilinearMap R M₁' M₂) ->ₗ[R] MultilinearMap R M₁ M₂) _ _ _
        (fun _ => LinearMap.module) _ where
  toFun := MultilinearMap.compLinearMapₗ
  map_update_add' := by
    intro _ f i f₁ f₂
    ext g x
    change (g fun j => update f i (f₁ + f₂) j <| x j) =
        (g fun j => update f i f₁ j <| x j) + g fun j => update f i f₂ j (x j)
    let c : Π (i : ι), (M₁ i ->ₗ[R] M₁' i) -> M₁' i := fun i f => f (x i)
    convert! g.map_update_add (fun j => f j (x j)) i (f₁ (x i)) (f₂ (x i)) with j j j
    · exact Function.apply_update c f i (f₁ + f₂) j
    · exact Function.apply_update c f i f₁ j
    · exact Function.apply_update c f i f₂ j
  map_update_smul' := by
    intro _ f i a f₀
    ext g x
    change (g fun j => update f i (a • f₀) j <| x j) = a • g fun j => update f i f₀ j (x j)
    let c : Π (i : ι), (M₁ i ->ₗ[R] M₁' i) -> M₁' i := fun i f => f (x i)
    convert! g.map_update_smul (fun j => f j (x j)) i a (f₀ (x i)) with j j j
    · exact Function.apply_update c f i (a • f₀) j
    · exact Function.apply_update c f i f₀ j

/--
Definition of `piLinearMap` / `piLinearMap` 的定义

English:
definition piLinearMap
  signature: :
  body: (LinearMap.applyₗ g).compMultilinearMap compLinearMapMultilinear
  map_add' := by simp
  map_smul' := by simp

中文:
定义 piLinearMap
  签名: :
  定义体: (LinearMap.applyₗ g).compMultilinearMap compLinearMapMultilinear
  map_add' := by simp
  map_smul' := by simp
-/
@[simps!] def piLinearMap :
    MultilinearMap R M₁' M₂ ->ₗ[R]
    MultilinearMap R (fun i => M₁ i ->ₗ[R] M₁' i) (MultilinearMap R M₁ M₂) where
  toFun g := (LinearMap.applyₗ g).compMultilinearMap compLinearMapMultilinear
  map_add' := by simp
  map_smul' := by simp

end

/--
theorem `map_piecewise_smul` / 定理 `map_piecewise_smul`

English:
theorem map_piecewise_smul
  given: [DecidableEq ι] (c : ι -> R) (m : forall i, M₁ i) (s : Finset ι)
  proof: by
  refine s.induction_on (by simp) ?_
  intro j s j_notMem_s Hrec
  have A :
    Function.update (s.piecewise (fun i => c i • m i) m) j (m j) =
      s.piecewise (fun i => c i • m i) m := by
    ext i
    by_cases h : i = j
    · rw [h]
      simp [j_notMem_s]
    · simp [h]
  rw [s.piecewise_inse

中文:
定理 map_piecewise_smul
  条件: [DecidableEq ι] (c : ι -> R) (m : 对任意 i, M₁ i) (s : 有限集 ι)
  证明: by
  refine s.induction_on (by simp) ?_
  intro j s j_notMem_s Hrec
  have A :
    Function.update (s.piecewise (fun i => c i • m i) m) j (m j) =
      s.piecewise (fun i => c i • m i) m := by
    ext i
    by_cases h : i = j
    · rw [h]
      simp [j_notMem_s]
    · simp [h]
  rw [s.piecewise_inse

Depends on / 依赖: Function, Function.update, f.map_update_smul, induction_on, j_notMem_s, map_update_smul, mul_smul, piecewise, piecewise_insert, s.induction_on, s.piecewise, s.piecewise_insert, update
-/
theorem map_piecewise_smul [DecidableEq ι] (c : ι -> R) (m : forall i, M₁ i) (s : Finset ι) :
    f (s.piecewise (fun i => c i • m i) m) = (∏ i in s, c i) • f m := by
  refine s.induction_on (by simp) ?_
  intro j s j_notMem_s Hrec
  have A :
    Function.update (s.piecewise (fun i => c i • m i) m) j (m j) =
      s.piecewise (fun i => c i • m i) m := by
    ext i
    by_cases h : i = j
    · rw [h]
      simp [j_notMem_s]
    · simp [h]
  rw [s.piecewise_insert]; rw [f.map_update_smul]; rw [A]; rw [Hrec]
  simp [j_notMem_s, mul_smul]

/--
theorem `map_smul_univ` / 定理 `map_smul_univ`

English:
theorem map_smul_univ
  given: [Fintype ι] (c : ι -> R) (m : forall i, M₁ i)
  proof: by
  classical simpa using map_piecewise_smul f c m Finset.univ

@[simp]

中文:
定理 map_smul_univ
  条件: [有限类型 ι] (c : ι -> R) (m : 对任意 i, M₁ i)
  证明: by
  classical simpa using map_piecewise_smul f c m Finset.univ

@[simp]

Depends on / 依赖: Finset, Finset.univ, classical, map_piecewise_smul
-/
theorem map_smul_univ [Fintype ι] (c : ι -> R) (m : forall i, M₁ i) :
    (f fun i => c i • m i) = (∏ i, c i) • f m := by
  classical simpa using map_piecewise_smul f c m Finset.univ

@[simp]
/--
theorem `map_update_smul_left` / 定理 `map_update_smul_left`

English:
theorem map_update_smul_left
  statement: [DecidableEq ι] [Fintype ι]
  proof: by
  have : f ((Finset.univ.erase i).piecewise (c • update m i x) (update m i x)) =
      (∏ _i in Finset.univ.erase i, c) • f (update m i x) :=
    map_piecewise_smul f _ _ _
  simpa [← Function.update_smul c m] using this

中文:
定理 map_update_smul_left
  结论: [DecidableEq ι] [有限类型 ι]
  证明: by
  have : f ((Finset.univ.erase i).piecewise (c • update m i x) (update m i x)) =
      (∏ _i in Finset.univ.erase i, c) • f (update m i x) :=
    map_piecewise_smul f _ _ _
  simpa [← Function.update_smul c m] using this

Depends on / 依赖: Finset, Finset.univ.erase, Function, Function.update_smul, map_piecewise_smul, piecewise, update, update_smul
-/
theorem map_update_smul_left [DecidableEq ι] [Fintype ι]
    (m : forall i, M₁ i) (i : ι) (c : R) (x : M₁ i) :
    f (update (c • m) i x) = c ^ (Fintype.card ι - 1) • f (update m i x) := by
  have : f ((Finset.univ.erase i).piecewise (c • update m i x) (update m i x)) =
      (∏ _i in Finset.univ.erase i, c) • f (update m i x) :=
    map_piecewise_smul f _ _ _
  simpa [← Function.update_smul c m] using this

/-- If two `R`-multilinear maps from `R` are equal on 1, then they are equal.

This is the multilinear version of `LinearMap.ext_ring`. -/
@[ext]
/--
theorem `ext_ring` / 定理 `ext_ring`

English:
theorem ext_ring
  given: [Finite ι] ⦃f g
  statement: MultilinearMap R (fun _ : ι => R) M₂⦄
  proof: by
  ext x
  obtain ⟨_⟩ := nonempty_fintype ι
  have hf := f.map_smul_univ x (fun _ => 1)
  have hg := g.map_smul_univ x (fun _ => 1)
  simp_all

中文:
定理 ext_ring
  条件: [有限 ι] ⦃f g
  结论: 多重线性映射 R (fun _ : ι => R) M₂⦄
  证明: by
  ext x
  obtain ⟨_⟩ := nonempty_fintype ι
  have hf := f.map_smul_univ x (fun _ => 1)
  have hg := g.map_smul_univ x (fun _ => 1)
  simp_all

Depends on / 依赖: f.map_smul_univ, g.map_smul_univ, map_smul_univ, nonempty_fintype
-/
theorem ext_ring [Finite ι] ⦃f g : MultilinearMap R (fun _ : ι => R) M₂⦄
    (h : f (fun _ => 1) = g (fun _ => 1)) : f = g := by
  ext x
  obtain ⟨_⟩ := nonempty_fintype ι
  have hf := f.map_smul_univ x (fun _ => 1)
  have hg := g.map_smul_univ x (fun _ => 1)
  simp_all

section

variable (R ι)
variable (A : Type*) [CommSemiring A] [Algebra R A] [Fintype ι]

/--
Definition of `mkPiAlgebra` / `mkPiAlgebra` 的定义

English:
definition mkPiAlgebra
  signature: : MultilinearMap R (fun _ : ι => A) A where
  body: ∏ i, m i
  map_update_add' m i x y := by simp [Finset.prod_update_of_mem, add_mul]
  map_update_smul' m i c x := by simp [Finset.prod_update_of_mem]

中文:
定义 mkPiAlgebra
  签名: : 多重线性映射 R (fun _ : ι => A) A where
  定义体: ∏ i, m i
  map_update_add' m i x y := by simp [Finset.prod_update_of_mem, add_mul]
  map_update_smul' m i c x := by simp [Finset.prod_update_of_mem]
-/
protected def mkPiAlgebra : MultilinearMap R (fun _ : ι => A) A where
  toFun m := ∏ i, m i
  map_update_add' m i x y := by simp [Finset.prod_update_of_mem, add_mul]
  map_update_smul' m i c x := by simp [Finset.prod_update_of_mem]

variable {R A ι}

@[simp]
/--
theorem `mkPiAlgebra_apply` / 定理 `mkPiAlgebra_apply`

English:
theorem mkPiAlgebra_apply
  given: (m : ι -> A)
  statement: MultilinearMap.mkPiAlgebra R ι A m = ∏ i, m i
  proof: rfl

中文:
定理 mkPiAlgebra_apply
  条件: (m : ι -> A)
  结论: 多重线性映射.mkPiAlgebra R ι A m = ∏ i, m i
  证明: rfl
-/
theorem mkPiAlgebra_apply (m : ι -> A) : MultilinearMap.mkPiAlgebra R ι A m = ∏ i, m i :=
  rfl

end

section

variable (R n)
variable (A : Type*) [Semiring A] [Algebra R A]

/--
Definition of `mkPiAlgebraFin` / `mkPiAlgebraFin` 的定义

English:
definition mkPiAlgebraFin
  signature: : MultilinearMap R (fun _ : Fin n => A) A
  body: MultilinearMap.mk' (fun m => (List.ofFn m).prod)
    (fun m i x y => by
      simp [List.ofFn_eq_map, (List.nodup_finRange n).map_update, List.prod_set, add_mul,
        mul_add, add_mul])
    (fun m i c x => by
      simp [List.ofFn_eq_map, (List.nodup_finRange n).map_update, List.prod_set])

中文:
定义 mkPiAlgebraFin
  签名: : 多重线性映射 R (fun _ : 有限集 n => A) A
  定义体: MultilinearMap.mk' (fun m => (List.ofFn m).prod)
    (fun m i x y => by
      simp [List.ofFn_eq_map, (List.nodup_finRange n).map_update, List.prod_set, add_mul,
        mul_add, add_mul])
    (fun m i c x => by
      simp [List.ofFn_eq_map, (List.nodup_finRange n).map_update, List.prod_set])
-/
protected def mkPiAlgebraFin : MultilinearMap R (fun _ : Fin n => A) A :=
  MultilinearMap.mk' (fun m => (List.ofFn m).prod)
    (fun m i x y => by
      simp [List.ofFn_eq_map, (List.nodup_finRange n).map_update, List.prod_set, add_mul,
        mul_add, add_mul])
    (fun m i c x => by
      simp [List.ofFn_eq_map, (List.nodup_finRange n).map_update, List.prod_set])

variable {R A n}

@[simp]
/--
theorem `mkPiAlgebraFin_apply` / 定理 `mkPiAlgebraFin_apply`

English:
theorem mkPiAlgebraFin_apply
  given: (m : Fin n -> A)
  proof: rfl

中文:
定理 mkPiAlgebraFin_apply
  条件: (m : 有限集 n -> A)
  证明: rfl
-/
theorem mkPiAlgebraFin_apply (m : Fin n -> A) :
    MultilinearMap.mkPiAlgebraFin R n A m = (List.ofFn m).prod :=
  rfl

/--
theorem `mkPiAlgebraFin_apply_const` / 定理 `mkPiAlgebraFin_apply_const`

English:
theorem mkPiAlgebraFin_apply_const
  given: (a : A)
  proof: by simp

中文:
定理 mkPiAlgebraFin_apply_const
  条件: (a : A)
  证明: by simp
-/
theorem mkPiAlgebraFin_apply_const (a : A) :
    (MultilinearMap.mkPiAlgebraFin R n A fun _ => a) = a ^ n := by simp

end

/--
Definition of `smulRight` / `smulRight` 的定义

English:
definition smulRight
  signature: (f : MultilinearMap R M₁ R) (z : M₂)
  body: (LinearMap.smulRight LinearMap.id z).compMultilinearMap f

@[simp]

中文:
定义 smulRight
  签名: (f : 多重线性映射 R M₁ R) (z : M₂)
  定义体: (LinearMap.smulRight LinearMap.id z).compMultilinearMap f

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id, LinearMap.smulRight, compMultilinearMap, smulRight
-/
def smulRight (f : MultilinearMap R M₁ R) (z : M₂) : MultilinearMap R M₁ M₂ :=
  (LinearMap.smulRight LinearMap.id z).compMultilinearMap f

@[simp]
/--
theorem `smulRight_apply` / 定理 `smulRight_apply`

English:
theorem smulRight_apply
  given: (f : MultilinearMap R M₁ R) (z : M₂) (m : forall i, M₁ i)
  proof: rfl

中文:
定理 smulRight_apply
  条件: (f : 多重线性映射 R M₁ R) (z : M₂) (m : 对任意 i, M₁ i)
  证明: rfl
-/
theorem smulRight_apply (f : MultilinearMap R M₁ R) (z : M₂) (m : forall i, M₁ i) :
    f.smulRight z m = f m • z :=
  rfl

variable (R ι)

/--
Definition of `mkPiRing` / `mkPiRing` 的定义

English:
definition mkPiRing
  signature: [Fintype ι] (z : M₂)
  body: (MultilinearMap.mkPiAlgebra R ι R).smulRight z

中文:
定义 mkPiRing
  签名: [有限类型 ι] (z : M₂)
  定义体: (MultilinearMap.mkPiAlgebra R ι R).smulRight z
-/
protected def mkPiRing [Fintype ι] (z : M₂) : MultilinearMap R (fun _ : ι => R) M₂ :=
  (MultilinearMap.mkPiAlgebra R ι R).smulRight z

variable {R ι}

@[simp]
/--
theorem `mkPiRing_apply` / 定理 `mkPiRing_apply`

English:
theorem mkPiRing_apply
  given: [Fintype ι] (z : M₂) (m : ι -> R)
  proof: rfl

中文:
定理 mkPiRing_apply
  条件: [有限类型 ι] (z : M₂) (m : ι -> R)
  证明: rfl
-/
theorem mkPiRing_apply [Fintype ι] (z : M₂) (m : ι -> R) :
    (MultilinearMap.mkPiRing R ι z : (ι -> R) -> M₂) m = (∏ i, m i) • z :=
  rfl

/--
theorem `mkPiRing_apply_one_eq_self` / 定理 `mkPiRing_apply_one_eq_self`

English:
theorem mkPiRing_apply_one_eq_self
  given: [Fintype ι] (f : MultilinearMap R (fun _ : ι => R) M₂)
  proof: by
  ext
  simp

中文:
定理 mkPiRing_apply_one_eq_self
  条件: [有限类型 ι] (f : 多重线性映射 R (fun _ : ι => R) M₂)
  证明: by
  ext
  simp
-/
theorem mkPiRing_apply_one_eq_self [Fintype ι] (f : MultilinearMap R (fun _ : ι => R) M₂) :
    MultilinearMap.mkPiRing R ι (f fun _ => 1) = f := by
  ext
  simp

/--
theorem `mkPiRing_eq_iff` / 定理 `mkPiRing_eq_iff`

English:
theorem mkPiRing_eq_iff
  given: [Fintype ι] {z₁ z₂ : M₂}
  proof: by
  simp_rw [MultilinearMap.ext_iff, mkPiRing_apply]
  constructor <;> intro h
  · simpa using h fun _ => 1
  · simp [h]

中文:
定理 mkPiRing_eq_iff
  条件: [有限类型 ι] {z₁ z₂ : M₂}
  证明: by
  simp_rw [MultilinearMap.ext_iff, mkPiRing_apply]
  constructor <;> intro h
  · simpa using h fun _ => 1
  · simp [h]

Depends on / 依赖: MultilinearMap, MultilinearMap.ext_iff, ext_iff, mkPiRing_apply, simp_rw
-/
theorem mkPiRing_eq_iff [Fintype ι] {z₁ z₂ : M₂} :
    MultilinearMap.mkPiRing R ι z₁ = MultilinearMap.mkPiRing R ι z₂ ↔ z₁ = z₂ := by
  simp_rw [MultilinearMap.ext_iff, mkPiRing_apply]
  constructor <;> intro h
  · simpa using h fun _ => 1
  · simp [h]

/--
theorem `mkPiRing_zero` / 定理 `mkPiRing_zero`

English:
theorem mkPiRing_zero
  given: [Fintype ι]
  statement: MultilinearMap.mkPiRing R ι (0 : M₂) = 0
  proof: by
  ext; rw [mkPiRing_apply, smul_zero, zero_apply]

中文:
定理 mkPiRing_zero
  条件: [有限类型 ι]
  结论: 多重线性映射.mkPiRing R ι (0 : M₂) = 0
  证明: by
  ext; rw [mkPiRing_apply, smul_zero, zero_apply]

Depends on / 依赖: mkPiRing_apply, smul_zero, zero_apply
-/
theorem mkPiRing_zero [Fintype ι] : MultilinearMap.mkPiRing R ι (0 : M₂) = 0 := by
  ext; rw [mkPiRing_apply, smul_zero, zero_apply]

/--
theorem `mkPiRing_eq_zero_iff` / 定理 `mkPiRing_eq_zero_iff`

English:
theorem mkPiRing_eq_zero_iff
  given: [Fintype ι] (z : M₂)
  statement: MultilinearMap.mkPiRing R ι z = 0 ↔ z = 0
  proof: by
  rw [← mkPiRing_zero]; rw [mkPiRing_eq_iff]

中文:
定理 mkPiRing_eq_zero_iff
  条件: [有限类型 ι] (z : M₂)
  结论: 多重线性映射.mkPiRing R ι z = 0 ↔ z = 0
  证明: by
  rw [← mkPiRing_zero]; rw [mkPiRing_eq_iff]

Depends on / 依赖: mkPiRing_eq_iff, mkPiRing_zero
-/
theorem mkPiRing_eq_zero_iff [Fintype ι] (z : M₂) : MultilinearMap.mkPiRing R ι z = 0 ↔ z = 0 := by
  rw [← mkPiRing_zero]; rw [mkPiRing_eq_iff]

end CommSemiring

section RangeAddCommGroup

variable [Semiring R] [forall i, AddCommMonoid (M₁ i)] [AddCommGroup M₂] [forall i, Module R (M₁ i)]
  [Module R M₂] (f g : MultilinearMap R M₁ M₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (MultilinearMap R M₁ M₂)
  body: ⟨fun f => ⟨fun m => -f m, fun m i x y => by simp [add_comm], fun m i c x => by simp⟩⟩

中文:
实例 :
  签名: 取负 (多重线性映射 R M₁ M₂)
  定义体: ⟨fun f => ⟨fun m => -f m, fun m i x y => by simp [add_comm], fun m i c x => by simp⟩⟩

Depends on / 依赖: add_comm
-/
instance : Neg (MultilinearMap R M₁ M₂) :=
  ⟨fun f => ⟨fun m => -f m, fun m i x y => by simp [add_comm], fun m i c x => by simp⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNegApply (MultilinearMap R M₁ M₂) (forall i, M₁ i) M₂
  body: rfl

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply

中文:
实例 :
  签名: 是NegApply (多重线性映射 R M₁ M₂) (对任意 i, M₁ i) M₂
  定义体: rfl

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply
-/
instance : IsNegApply (MultilinearMap R M₁ M₂) (forall i, M₁ i) M₂ where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (MultilinearMap R M₁ M₂)
  body: ⟨fun f g =>
    ⟨fun m => f m - g m, fun m i x y => by
      simp only [MultilinearMap.map_update_add, sub_eq_add_neg, neg_add]
      abel,
      fun m i c x => by simp only [MultilinearMap.map_update_smul, smul_sub]⟩⟩

中文:
实例 :
  签名: 减法 (多重线性映射 R M₁ M₂)
  定义体: ⟨fun f g =>
    ⟨fun m => f m - g m, fun m i x y => by
      simp only [MultilinearMap.map_update_add, sub_eq_add_neg, neg_add]
      abel,
      fun m i c x => by simp only [MultilinearMap.map_update_smul, smul_sub]⟩⟩

Depends on / 依赖: MultilinearMap, MultilinearMap.map_update_add, MultilinearMap.map_update_smul, map_update_add, map_update_smul, neg_add, smul_sub, sub_eq_add_neg
-/
instance : Sub (MultilinearMap R M₁ M₂) :=
  ⟨fun f g =>
    ⟨fun m => f m - g m, fun m i x y => by
      simp only [MultilinearMap.map_update_add, sub_eq_add_neg, neg_add]
      abel,
      fun m i c x => by simp only [MultilinearMap.map_update_smul, smul_sub]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSubApply (MultilinearMap R M₁ M₂) (forall i, M₁ i) M₂
  body: rfl

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply

中文:
实例 :
  签名: 是SubApply (多重线性映射 R M₁ M₂) (对任意 i, M₁ i) M₂
  定义体: rfl

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply
-/
instance : IsSubApply (MultilinearMap R M₁ M₂) (forall i, M₁ i) M₂ where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (MultilinearMap R M₁ M₂)
  body: fast_instance% FunLike.addCommGroup

中文:
实例 :
  签名: 加法交换群 (多重线性映射 R M₁ M₂)
  定义体: fast_instance% FunLike.addCommGroup

Depends on / 依赖: FunLike, FunLike.addCommGroup, addCommGroup, fast_instance
-/
instance : AddCommGroup (MultilinearMap R M₁ M₂) := fast_instance% FunLike.addCommGroup

end RangeAddCommGroup

section AddCommGroup

variable [Semiring R] [forall i, AddCommGroup (M₁ i)] [AddCommGroup M₂] [forall i, Module R (M₁ i)]
  [Module R M₂] (f : MultilinearMap R M₁ M₂)

@[simp]
/--
theorem `map_update_neg` / 定理 `map_update_neg`

English:
theorem map_update_neg
  given: [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x : M₁ i)
  proof: eq_neg_of_add_eq_zero_left by
    rw [← MultilinearMap.map_update_add]; rw [neg_add_cancel]; rw [f.map_coord_zero i (update_self i 0 m)]

@[simp]

中文:
定理 map_update_neg
  条件: [DecidableEq ι] (m : 对任意 i, M₁ i) (i : ι) (x : M₁ i)
  证明: eq_neg_of_add_eq_zero_left by
    rw [← MultilinearMap.map_update_add]; rw [neg_add_cancel]; rw [f.map_coord_zero i (update_self i 0 m)]

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.map_update_add, eq_neg_of_add_eq_zero_left, f.map_coord_zero, map_coord_zero, map_update_add, neg_add_cancel, update_self
-/
theorem map_update_neg [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x : M₁ i) :
    f (update m i (-x)) = -f (update m i x) :=
eq_neg_of_add_eq_zero_left by
    rw [← MultilinearMap.map_update_add]; rw [neg_add_cancel]; rw [f.map_coord_zero i (update_self i 0 m)]

@[simp]
/--
theorem `map_update_sub` / 定理 `map_update_sub`

English:
theorem map_update_sub
  given: [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x y : M₁ i)
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [MultilinearMap.map_update_add]; rw [map_update_neg]

中文:
定理 map_update_sub
  条件: [DecidableEq ι] (m : 对任意 i, M₁ i) (i : ι) (x y : M₁ i)
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [MultilinearMap.map_update_add]; rw [map_update_neg]

Depends on / 依赖: MultilinearMap, MultilinearMap.map_update_add, map_update_add, map_update_neg, sub_eq_add_neg
-/
theorem map_update_sub [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x - y)) = f (update m i x) - f (update m i y) := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [MultilinearMap.map_update_add]; rw [map_update_neg]

/--
lemma `map_update` / 引理 `map_update`

English:
lemma map_update
  given: [DecidableEq ι] (x : (i : ι) -> M₁ i) (i : ι) (v : M₁ i)
  proof: by
  rw [map_update_sub]; rw [update_eq_self]; rw [sub_sub_cancel]

中文:
引理 map_update
  条件: [DecidableEq ι] (x : (i : ι) -> M₁ i) (i : ι) (v : M₁ i)
  证明: by
  rw [map_update_sub]; rw [update_eq_self]; rw [sub_sub_cancel]

Depends on / 依赖: map_update_sub, sub_sub_cancel, update_eq_self
-/
lemma map_update [DecidableEq ι] (x : (i : ι) -> M₁ i) (i : ι) (v : M₁ i) :
    f (update x i v) = f x - f (update x i (x i - v)) := by
  rw [map_update_sub]; rw [update_eq_self]; rw [sub_sub_cancel]

/--
lemma `map_sub_map_piecewise` / 引理 `map_sub_map_piecewise`

English:
lemma map_sub_map_piecewise
  given: [LinearOrder ι] (a b : (i : ι) -> M₁ i) (s : Finset ι)
  proof: by
  induction s using induction_on_min with
  | empty => rw [Finset.piecewise_empty, sum_empty, sub_self]
  | insert k s hk ih => ?_
  rw [Finset.piecewise_insert]; rw [map_update]; rw [← sub_add]; rw [ih]; rw [add_comm]; rw [sum_insert (lt_irrefl _ <| hk k ·)]
  simp_rw [s.mem_insert]
  congr 1
  

中文:
引理 map_sub_map_piecewise
  条件: [线性序 ι] (a b : (i : ι) -> M₁ i) (s : 有限集 ι)
  证明: by
  induction s using induction_on_min with
  | empty => rw [Finset.piecewise_empty, sum_empty, sub_self]
  | insert k s hk ih => ?_
  rw [Finset.piecewise_insert]; rw [map_update]; rw [← sub_add]; rw [ih]; rw [add_comm]; rw [sum_insert (lt_irrefl _ <| hk k ·)]
  simp_rw [s.mem_insert]
  congr 1
  

Depends on / 依赖: Finset, Finset.piecewise_empty, Finset.piecewise_eq_of_notMem, Finset.piecewise_insert, add_comm, induction_on_min, insert, lt_irrefl, map_update, mem_insert, not_gt, piecew, piecewise_empty, piecewise_eq_of_notMem, piecewise_insert, s.mem_insert, s.piecew, simp_rw, split_ifs, sub_add
-/
lemma map_sub_map_piecewise [LinearOrder ι] (a b : (i : ι) -> M₁ i) (s : Finset ι) :
    f a - f (s.piecewise b a) =
    ∑ i in s, f (fun j => if j in s -> j < i then a j else if i = j then a j - b j else b j) := by
  induction s using induction_on_min with
  | empty => rw [Finset.piecewise_empty, sum_empty, sub_self]
  | insert k s hk ih => ?_
  rw [Finset.piecewise_insert]; rw [map_update]; rw [← sub_add]; rw [ih]; rw [add_comm]; rw [sum_insert (lt_irrefl _ <| hk k ·)]
  simp_rw [s.mem_insert]
  congr 1
  · congr; ext i; split_ifs with h₁ h₂
    · rw [update_of_ne, Finset.piecewise_eq_of_notMem]
      · exact fun h => (hk i h).not_gt (h₁ <| .inr h)
      · exact fun h => (h₁ <| .inl h).ne h
    · cases h₂
      rw [update_self]; rw [s.piecewise_eq_of_notMem _ _ (lt_irrefl _ <| hk k ·)]
    · push Not at h₁
      rw [update_of_ne (Ne.symm h₂)]; rw [s.piecewise_eq_of_mem _ _ (h₁.1.resolve_left <| Ne.symm h₂)]
  · apply sum_congr rfl
    grind

/--
lemma `map_piecewise_sub_map_piecewise` / 引理 `map_piecewise_sub_map_piecewise`

English:
lemma map_piecewise_sub_map_piecewise
  given: [LinearOrder ι] (a b v : (i : ι) -> M₁ i) (s : Finset ι)
  proof: by
  rw [← s.piecewise_idem_right b a]; rw [map_sub_map_piecewise]
refine Finset.sum_congr rfl fun i hi => congr_arg f funext fun j => ?_
  by_cases hjs : j in s
  · rw [if_pos hjs]; by_cases hji : j < i
    · rw [if_pos fun _ => hji, if_pos hji, s.piecewise_eq_of_mem _ _ hjs]
    rw [if_neg (Classi

中文:
引理 map_piecewise_sub_map_piecewise
  条件: [线性序 ι] (a b v : (i : ι) -> M₁ i) (s : 有限集 ι)
  证明: by
  rw [← s.piecewise_idem_right b a]; rw [map_sub_map_piecewise]
refine Finset.sum_congr rfl fun i hi => congr_arg f funext fun j => ?_
  by_cases hjs : j in s
  · rw [if_pos hjs]; by_cases hji : j < i
    · rw [if_pos fun _ => hji, if_pos hji, s.piecewise_eq_of_mem _ _ hjs]
    rw [if_neg (Classi

Depends on / 依赖: Classical, Classical.not_imp.mpr, Finset, Finset.sum_congr, congr_arg, eq_or_ne, hij.symm, if_neg, if_pos, map_sub_map_piecewise, not_imp, piecewise_eq_of_mem, piecewise_idem_right, s.piecewise_eq_of_mem, s.piecewise_idem_right, sInf_caratheodory, sum_congr, toMeasure, toOuterMeasure
-/
lemma map_piecewise_sub_map_piecewise [LinearOrder ι] (a b v : (i : ι) -> M₁ i) (s : Finset ι) :
    f (s.piecewise a v) - f (s.piecewise b v) = ∑ i in s, f
      fun j => if j in s then if j < i then a j else if j = i then a j - b j else b j else v j := by
  rw [← s.piecewise_idem_right b a]; rw [map_sub_map_piecewise]
refine Finset.sum_congr rfl fun i hi => congr_arg f funext fun j => ?_
  by_cases hjs : j in s
  · rw [if_pos hjs]; by_cases hji : j < i
    · rw [if_pos fun _ => hji, if_pos hji, s.piecewise_eq_of_mem _ _ hjs]
    rw [if_neg (Classical.not_imp.mpr ⟨hjs]; rw [hji⟩)]; rw [if_neg hji]
    obtain rfl | hij := eq_or_ne i j
    · rw [if_pos rfl, if_pos rfl, s.piecewise_eq_of_mem _ _ hi]
    · rw [if_neg hij, if_neg hij.symm]
  · rw [if_neg hjs, if_pos fun h => (hjs h).elim, s.piecewise_eq_of_notMem _ _ hjs]

open Finset in
/--
lemma `map_add_eq_map_add_linearDeriv_add` / 引理 `map_add_eq_map_add_linearDeriv_add`

English:
lemma map_add_eq_map_add_linearDeriv_add
  given: [DecidableEq ι] [Fintype ι] (x h : (i : ι) -> M₁ i)
  proof: by
  rw [add_comm]; rw [map_add_univ]; rw [← Finset.powerset_univ]; rw [← sum_filter_add_sum_filter_not _ (2 <= #·)]
  simp_rw [not_le, Nat.lt_succ_iff, le_iff_lt_or_eq (b := 1), Nat.lt_one_iff, filter_or,
    ← powersetCard_eq_filter, sum_union (univ.pairwise_disjoint_powersetCard zero_ne_one),
   

中文:
引理 map_add_eq_map_add_linearDeriv_add
  条件: [DecidableEq ι] [有限类型 ι] (x h : (i : ι) -> M₁ i)
  证明: by
  rw [add_comm]; rw [map_add_univ]; rw [← Finset.powerset_univ]; rw [← sum_filter_add_sum_filter_not _ (2 <= #·)]
  simp_rw [not_le, Nat.lt_succ_iff, le_iff_lt_or_eq (b := 1), Nat.lt_one_iff, filter_or,
    ← powersetCard_eq_filter, sum_union (univ.pairwise_disjoint_powersetCard zero_ne_one),
   

Depends on / 依赖: Embedding, Finset, Finset.piecewise_empty, Finset.piecewise_singleton, Finset.powerset_univ, Function, Function.Embedding.coeFn_mk, Nat.lt_one_iff, Nat.lt_succ_iff, add_comm, coeFn_mk, filter_or, le_iff_lt_or_eq, linearDeriv_apply, lt_one_iff, lt_succ_iff, map_add_univ, not_le, pairwise_disjoint_powersetCard, piecewise_empty
-/
lemma map_add_eq_map_add_linearDeriv_add [DecidableEq ι] [Fintype ι] (x h : (i : ι) -> M₁ i) :
    f (x + h) = f x + f.linearDeriv x h + ∑ s with 2 <= #s, f (s.piecewise h x) := by
  rw [add_comm]; rw [map_add_univ]; rw [← Finset.powerset_univ]; rw [← sum_filter_add_sum_filter_not _ (2 <= #·)]
  simp_rw [not_le, Nat.lt_succ_iff, le_iff_lt_or_eq (b := 1), Nat.lt_one_iff, filter_or,
    ← powersetCard_eq_filter, sum_union (univ.pairwise_disjoint_powersetCard zero_ne_one),
    powersetCard_zero, powersetCard_one, sum_singleton, Finset.piecewise_empty, sum_map,
    Function.Embedding.coeFn_mk, Finset.piecewise_singleton, linearDeriv_apply, add_comm]

open Finset in
/--
lemma `map_add_sub_map_add_sub_linearDeriv` / 引理 `map_add_sub_map_add_sub_linearDeriv`

English:
lemma map_add_sub_map_add_sub_linearDeriv
  given: [DecidableEq ι] [Fintype ι] (x h h' : (i : ι) -> M₁ i)
  proof: by
  simp_rw [map_add_eq_map_add_linearDeriv_add, add_assoc, add_sub_add_comm, sub_self, zero_add,
    ← map_sub, add_sub_cancel_left, sum_sub_distrib]

中文:
引理 map_add_sub_map_add_sub_linearDeriv
  条件: [DecidableEq ι] [有限类型 ι] (x h h' : (i : ι) -> M₁ i)
  证明: by
  simp_rw [map_add_eq_map_add_linearDeriv_add, add_assoc, add_sub_add_comm, sub_self, zero_add,
    ← map_sub, add_sub_cancel_left, sum_sub_distrib]

Depends on / 依赖: add_assoc, add_sub_add_comm, add_sub_cancel_left, map_add_eq_map_add_linearDeriv_add, map_sub, simp_rw, sub_self, sum_sub_distrib, zero_add
-/
lemma map_add_sub_map_add_sub_linearDeriv [DecidableEq ι] [Fintype ι] (x h h' : (i : ι) -> M₁ i) :
    f (x + h) - f (x + h') - f.linearDeriv x (h - h') =
    ∑ s with 2 <= #s, (f (s.piecewise h x) - f (s.piecewise h' x)) := by
  simp_rw [map_add_eq_map_add_linearDeriv_add, add_assoc, add_sub_add_comm, sub_self, zero_add,
    ← map_sub, add_sub_cancel_left, sum_sub_distrib]

end AddCommGroup

section CommSemiring

variable [CommSemiring R] [forall i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [forall i, Module R (M₁ i)]
  [Module R M₂]

/--
Definition of `piRingEquiv` / `piRingEquiv` 的定义

English:
definition piRingEquiv
  signature: [Fintype ι]
  body: MultilinearMap.mkPiRing R ι z
  invFun f := f fun _ => 1
  map_add' z z' := by
    ext
    simp
  map_smul' c z := by
    ext
    simp
  left_inv z := by simp
  right_inv f := f.mkPiRing_apply_one_eq_self

中文:
定义 piRingEquiv
  签名: [有限类型 ι]
  定义体: MultilinearMap.mkPiRing R ι z
  invFun f := f fun _ => 1
  map_add' z z' := by
    ext
    simp
  map_smul' c z := by
    ext
    simp
  left_inv z := by simp
  right_inv f := f.mkPiRing_apply_one_eq_self
-/
protected def piRingEquiv [Fintype ι] : M₂ ≃ₗ[R] MultilinearMap R (fun _ : ι => R) M₂ where
  toFun z := MultilinearMap.mkPiRing R ι z
  invFun f := f fun _ => 1
  map_add' z z' := by
    ext
    simp
  map_smul' c z := by
    ext
    simp
  left_inv z := by simp
  right_inv f := f.mkPiRing_apply_one_eq_self

end CommSemiring

section Submodule

variable [Ring R] [forall i, AddCommMonoid (M₁ i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [forall i, Module R (M₁ i)] [Module R M'] [Module R M₂]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : forall i, Submodule R (M₁ i))
  body: f '' { v | forall i, v i in p i }
  smul_mem' := fun c _ ⟨x, hx, hf⟩ => by
    let ⟨i⟩ := ‹Nonempty ι›
    let := Classical.decEq ι
    refine ⟨update x i (c • x i), fun j => if hij : j = i then ?_ else ?_, hf ▸ ?_⟩
    · rw [hij, update_self]
      exact (p i).smul_mem _ (hx i)
    · rw [update_of_

中文:
定义 map
  签名: [非空 ι] (f : 多重线性映射 R M₁ M₂) (p : 对任意 i, 子模 R (M₁ i))
  定义体: f '' { v | forall i, v i in p i }
  smul_mem' := fun c _ ⟨x, hx, hf⟩ => by
    let ⟨i⟩ := ‹Nonempty ι›
    let := Classical.decEq ι
    refine ⟨update x i (c • x i), fun j => if hij : j = i then ?_ else ?_, hf ▸ ?_⟩
    · rw [hij, update_self]
      exact (p i).smul_mem _ (hx i)
    · rw [update_of_
-/
def map [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : forall i, Submodule R (M₁ i)) :
    SubMulAction R M₂ where
  carrier := f '' { v | forall i, v i in p i }
  smul_mem' := fun c _ ⟨x, hx, hf⟩ => by
    let ⟨i⟩ := ‹Nonempty ι›
    let := Classical.decEq ι
    refine ⟨update x i (c • x i), fun j => if hij : j = i then ?_ else ?_, hf ▸ ?_⟩
    · rw [hij, update_self]
      exact (p i).smul_mem _ (hx i)
    · rw [update_of_ne hij]
      exact hx j
    · rw [f.map_update_smul, update_eq_self]

/--
theorem `map_nonempty` / 定理 `map_nonempty`

English:
theorem map_nonempty
  given: [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : forall i, Submodule R (M₁ i))
  proof: ⟨f 0, 0, fun i => (p i).zero_mem, rfl⟩

中文:
定理 map_nonempty
  条件: [非空 ι] (f : 多重线性映射 R M₁ M₂) (p : 对任意 i, 子模 R (M₁ i))
  证明: ⟨f 0, 0, fun i => (p i).zero_mem, rfl⟩

Depends on / 依赖: zero_mem
-/
theorem map_nonempty [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : forall i, Submodule R (M₁ i)) :
    (map f p : Set M₂).Nonempty :=
  ⟨f 0, 0, fun i => (p i).zero_mem, rfl⟩

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: [Nonempty ι] (f : MultilinearMap R M₁ M₂)
  body: f.map fun _ => ⊤

中文:
定义 range
  签名: [非空 ι] (f : 多重线性映射 R M₁ M₂)
  定义体: f.map fun _ => ⊤

Depends on / 依赖: f.map
-/
def range [Nonempty ι] (f : MultilinearMap R M₁ M₂) : SubMulAction R M₂ :=
  f.map fun _ => ⊤

end Submodule

end MultilinearMap
