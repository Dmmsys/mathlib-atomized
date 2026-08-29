/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Decompositions of additive monoids, groups, and modules into direct sums

## Main definitions

* `DirectSum.Decomposition ℳ`: A typeclass to provide a constructive decomposition from
  an additive monoid `M` into a family of additive submonoids `ℳ`
* `DirectSum.decompose ℳ`: The canonical equivalence provided by the above typeclass


## Main statements

* `DirectSum.Decomposition.isInternal`: The link to `DirectSum.IsInternal`.

## Implementation details

As we want to talk about different types of decomposition (additive monoids, modules, rings, ...),
we choose to avoid heavily bundling `DirectSum.decompose`, instead making copies for the
`AddEquiv`, `LinearEquiv`, etc. This means we have to repeat statements that follow from these
bundled homs, but means we don't have to repeat statements for different types of decomposition.
-/

@[expose] public section


variable {ι R M σ : Type*}

open DirectSum

namespace DirectSum

section AddCommMonoid

variable [DecidableEq ι] [AddCommMonoid M]
variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι -> σ)

/--
Definition of `Decomposition` / `Decomposition` 的定义

English:
class Decomposition
  parameters: where
  axioms and operations (3):
    - decompose' : M -> ⨁ i, ℳ i
    - left_inv : Function.LeftInverse (DirectSum.coeAddMonoidHom ℳ) decompose'
    - right_inv : Function.RightInverse (DirectSum.coeAddMonoidHom ℳ) decompose'

中文:
类 Decomposition
  参数: where
  公理与运算 (3 个):
    - decompose' : M -> ⨁ i, ℳ i
    - left_inv : Function.LeftInverse (DirectSum.coeAddMonoidHom ℳ) decompose'
    - right_inv : Function.RightInverse (DirectSum.coeAddMonoidHom ℳ) decompose'
-/
class Decomposition where
  decompose' : M -> ⨁ i, ℳ i
  left_inv : Function.LeftInverse (DirectSum.coeAddMonoidHom ℳ) decompose'
  right_inv : Function.RightInverse (DirectSum.coeAddMonoidHom ℳ) decompose'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (Decomposition ℳ)
  body: ⟨fun x y => by
    obtain ⟨_, _, xr⟩ := x
    obtain ⟨_, yl, _⟩ := y
    congr
    exact Function.LeftInverse.eq_rightInverse xr yl⟩

中文:
实例 :
  签名: Subsingleton (Decomposition ℳ)
  定义体: ⟨fun x y => by
    obtain ⟨_, _, xr⟩ := x
    obtain ⟨_, yl, _⟩ := y
    congr
    exact Function.LeftInverse.eq_rightInverse xr yl⟩

Depends on / 依赖: Function, Function.LeftInverse.eq_rightInverse, LeftInverse, eq_rightInverse
-/
instance : Subsingleton (Decomposition ℳ) :=
  ⟨fun x y => by
    obtain ⟨_, _, xr⟩ := x
    obtain ⟨_, yl, _⟩ := y
    congr
    exact Function.LeftInverse.eq_rightInverse xr yl⟩

/--
Definition of `Decomposition.ofAddHom` / `Decomposition.ofAddHom` 的定义

English:
abbreviation Decomposition.ofAddHom
  signature: (decompose : M ->+ ⨁ i, ℳ i)
  body: decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv

中文:
缩写 Decomposition.ofAddHom
  签名: (decompose : M ->+ ⨁ i, ℳ i)
  定义体: decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv

Depends on / 依赖: decompose
-/
abbrev Decomposition.ofAddHom (decompose : M ->+ ⨁ i, ℳ i)
    (h_left_inv : (DirectSum.coeAddMonoidHom ℳ).comp decompose = .id _)
    (h_right_inv : decompose.comp (DirectSum.coeAddMonoidHom ℳ) = .id _) : Decomposition ℳ where
  decompose' := decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv

/-- Noncomputably conjure a decomposition instance from a `DirectSum.IsInternal` proof. -/
@[instance_reducible]
/--
Definition of `IsInternal.chooseDecomposition` / `IsInternal.chooseDecomposition` 的定义

English:
definition IsInternal.chooseDecomposition
  signature: (h : IsInternal ℳ)
  body: (Equiv.ofBijective _ h).symm
  left_inv := (Equiv.ofBijective _ h).right_inv
  right_inv := (Equiv.ofBijective _ h).left_inv

中文:
定义 IsInternal.chooseDecomposition
  签名: (h : Is整数ernal ℳ)
  定义体: (Equiv.ofBijective _ h).symm
  left_inv := (Equiv.ofBijective _ h).right_inv
  right_inv := (Equiv.ofBijective _ h).left_inv

Depends on / 依赖: Equiv.ofBijective, ofBijective
-/
noncomputable def IsInternal.chooseDecomposition (h : IsInternal ℳ) :
    DirectSum.Decomposition ℳ where
  decompose' := (Equiv.ofBijective _ h).symm
  left_inv := (Equiv.ofBijective _ h).right_inv
  right_inv := (Equiv.ofBijective _ h).left_inv

variable [Decomposition ℳ]

/--
theorem `Decomposition.isInternal` / 定理 `Decomposition.isInternal`

English:
theorem Decomposition.isInternal
  statement: DirectSum.IsInternal ℳ
  proof: ⟨Decomposition.right_inv.injective, Decomposition.left_inv.surjective⟩

中文:
定理 Decomposition.isInternal
  结论: DirectSum.Is整数ernal ℳ
  证明: ⟨Decomposition.right_inv.injective, Decomposition.left_inv.surjective⟩
-/
protected theorem Decomposition.isInternal : DirectSum.IsInternal ℳ :=
  ⟨Decomposition.right_inv.injective, Decomposition.left_inv.surjective⟩

/--
Definition of `decompose` / `decompose` 的定义

English:
definition decompose
  signature: : M ≃ ⨁ i, ℳ i where
  body: Decomposition.decompose'
  invFun := DirectSum.coeAddMonoidHom ℳ
  left_inv := Decomposition.left_inv
  right_inv := Decomposition.right_inv

omit [AddSubmonoidClass σ M] in

中文:
定义 decompose
  签名: : M ≃ ⨁ i, ℳ i where
  定义体: Decomposition.decompose'
  invFun := DirectSum.coeAddMonoidHom ℳ
  left_inv := Decomposition.left_inv
  right_inv := Decomposition.right_inv

omit [AddSubmonoidClass σ M] in

Depends on / 依赖: Decomposition, Decomposition.decompose, decompose
-/
def decompose : M ≃ ⨁ i, ℳ i where
  toFun := Decomposition.decompose'
  invFun := DirectSum.coeAddMonoidHom ℳ
  left_inv := Decomposition.left_inv
  right_inv := Decomposition.right_inv

omit [AddSubmonoidClass σ M] in
/--
Definition of `SetLike.IsHomogeneous` / `SetLike.IsHomogeneous` 的定义

English:
definition SetLike.IsHomogeneous
  signature: {P : Type*} [SetLike P M] (p : P)
  body: forall (i : ι) ⦃m : M⦄, m in p -> (DirectSum.decompose ℳ m i : M) in p

@[elab_as_elim]

中文:
定义 SetLike.IsHomogeneous
  签名: {P : 类型} [SetLike P M] (p : P)
  定义体: forall (i : ι) ⦃m : M⦄, m in p -> (DirectSum.decompose ℳ m i : M) in p

@[elab_as_elim]

Depends on / 依赖: DirectSum, DirectSum.decompose, decompose
-/
def SetLike.IsHomogeneous {P : Type*} [SetLike P M] (p : P) : Prop :=
  forall (i : ι) ⦃m : M⦄, m in p -> (DirectSum.decompose ℳ m i : M) in p

@[elab_as_elim]
/--
theorem `Decomposition.inductionOn` / 定理 `Decomposition.inductionOn`

English:
theorem Decomposition.inductionOn
  statement: {motive : M -> Prop} (zero : motive 0)
  proof: by
  let ℳ' : ι -> AddSubmonoid M := fun i =>
    (⟨⟨ℳ i, fun x y => AddMemClass.add_mem x y⟩, (ZeroMemClass.zero_mem _)⟩ : AddSubmonoid M)
  have t : DirectSum.Decomposition ℳ' :=
    { decompose' := DirectSum.decompose ℳ
      left_inv := fun _ => (decompose ℳ).left_inv _
      right_inv := fun _ 

中文:
定理 Decomposition.inductionOn
  结论: {motive : M -> 命题} (zero : motive 0)
  证明: by
  let ℳ' : ι -> AddSubmonoid M := fun i =>
    (⟨⟨ℳ i, fun x y => AddMemClass.add_mem x y⟩, (ZeroMemClass.zero_mem _)⟩ : AddSubmonoid M)
  have t : DirectSum.Decomposition ℳ' :=
    { decompose' := DirectSum.decompose ℳ
      left_inv := fun _ => (decompose ℳ).left_inv _
      right_inv := fun _ 
-/
protected theorem Decomposition.inductionOn {motive : M -> Prop} (zero : motive 0)
    (homogeneous : forall {i} (m : ℳ i), motive (m : M))
    (add : forall m m' : M, motive m -> motive m' -> motive (m + m')) : forall m, motive m := by
  let ℳ' : ι -> AddSubmonoid M := fun i =>
    (⟨⟨ℳ i, fun x y => AddMemClass.add_mem x y⟩, (ZeroMemClass.zero_mem _)⟩ : AddSubmonoid M)
  have t : DirectSum.Decomposition ℳ' :=
    { decompose' := DirectSum.decompose ℳ
      left_inv := fun _ => (decompose ℳ).left_inv _
      right_inv := fun _ => (decompose ℳ).right_inv _ }
  have mem : forall m, m in iSup ℳ' := fun _m =>
    (DirectSum.IsInternal.addSubmonoid_iSup_eq_top ℳ' (Decomposition.isInternal ℳ')).symm ▸ trivial
  -- Porting note: needs to use @ even though no implicit argument is provided
  exact fun m => @AddSubmonoid.iSup_induction _ _ _ ℳ' _ _ (mem m)
    (fun i m h => homogeneous ⟨m, h⟩) zero add
-- exact fun m ↦
-- AddSubmonoid.iSup_induction ℳ' (mem m) (fun i m h ↦ h_homogeneous ⟨m, h⟩) h_zero h_add

@[simp]
/--
theorem `Decomposition.decompose'_eq` / 定理 `Decomposition.decompose'_eq`

English:
theorem Decomposition.decompose'_eq
  statement: Decomposition.decompose' = decompose ℳ
  proof: rfl

@[simp]

中文:
定理 Decomposition.decompose'_eq
  结论: Decomposition.decompose' = decompose ℳ
  证明: rfl

@[simp]
-/
theorem Decomposition.decompose'_eq : Decomposition.decompose' = decompose ℳ := rfl

@[simp]
/--
theorem `decompose_symm_of` / 定理 `decompose_symm_of`

English:
theorem decompose_symm_of
  given: {i : ι} (x : ℳ i)
  statement: (decompose ℳ).symm (DirectSum.of _ i x) = x
  proof: DirectSum.coeAddMonoidHom_of ℳ _ _

@[simp]

中文:
定理 decompose_symm_of
  条件: {i : ι} (x : ℳ i)
  结论: (decompose ℳ).symm (DirectSum.of _ i x) = x
  证明: DirectSum.coeAddMonoidHom_of ℳ _ _

@[simp]

Depends on / 依赖: DirectSum, DirectSum.coeAddMonoidHom_of, coeAddMonoidHom_of
-/
theorem decompose_symm_of {i : ι} (x : ℳ i) : (decompose ℳ).symm (DirectSum.of _ i x) = x :=
  DirectSum.coeAddMonoidHom_of ℳ _ _

@[simp]
/--
theorem `decompose_coe` / 定理 `decompose_coe`

English:
theorem decompose_coe
  given: {i : ι} (x : ℳ i)
  statement: decompose ℳ (x : M) = DirectSum.of _ i x
  proof: by
  rw [← decompose_symm_of _]; rw [Equiv.apply_symm_apply]

中文:
定理 decompose_coe
  条件: {i : ι} (x : ℳ i)
  结论: decompose ℳ (x : M) = DirectSum.of _ i x
  证明: by
  rw [← decompose_symm_of _]; rw [Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, decompose_symm_of
-/
theorem decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (x : M) = DirectSum.of _ i x := by
  rw [← decompose_symm_of _]; rw [Equiv.apply_symm_apply]

/--
theorem `decompose_of_mem` / 定理 `decompose_of_mem`

English:
theorem decompose_of_mem
  given: {x : M} {i : ι} (hx : x in ℳ i)
  proof: decompose_coe _ ⟨x, hx⟩

中文:
定理 decompose_of_mem
  条件: {x : M} {i : ι} (hx : x in ℳ i)
  证明: decompose_coe _ ⟨x, hx⟩

Depends on / 依赖: decompose_coe
-/
theorem decompose_of_mem {x : M} {i : ι} (hx : x in ℳ i) :
    decompose ℳ x = DirectSum.of (fun i => ℳ i) i ⟨x, hx⟩ :=
  decompose_coe _ ⟨x, hx⟩

/--
theorem `decompose_of_mem_same` / 定理 `decompose_of_mem_same`

English:
theorem decompose_of_mem_same
  given: {x : M} {i : ι} (hx : x in ℳ i)
  statement: (decompose ℳ x i : M) = x
  proof: by
  rw [decompose_of_mem _ hx]; rw [DirectSum.of_eq_same]; rw [Subtype.coe_mk]

中文:
定理 decompose_of_mem_same
  条件: {x : M} {i : ι} (hx : x in ℳ i)
  结论: (decompose ℳ x i : M) = x
  证明: by
  rw [decompose_of_mem _ hx]; rw [DirectSum.of_eq_same]; rw [Subtype.coe_mk]

Depends on / 依赖: DirectSum, DirectSum.of_eq_same, Subtype, Subtype.coe_mk, coe_mk, decompose_of_mem, of_eq_same
-/
theorem decompose_of_mem_same {x : M} {i : ι} (hx : x in ℳ i) : (decompose ℳ x i : M) = x := by
  rw [decompose_of_mem _ hx]; rw [DirectSum.of_eq_same]; rw [Subtype.coe_mk]

/--
theorem `decompose_of_mem_ne` / 定理 `decompose_of_mem_ne`

English:
theorem decompose_of_mem_ne
  given: {x : M} {i j : ι} (hx : x in ℳ i) (hij : i != j)
  proof: by
  rw [decompose_of_mem _ hx]; rw [DirectSum.of_eq_of_ne _ _ _ hij.symm]; rw [ZeroMemClass.coe_zero]

中文:
定理 decompose_of_mem_ne
  条件: {x : M} {i j : ι} (hx : x in ℳ i) (hij : i != j)
  证明: by
  rw [decompose_of_mem _ hx]; rw [DirectSum.of_eq_of_ne _ _ _ hij.symm]; rw [ZeroMemClass.coe_zero]

Depends on / 依赖: DirectSum, DirectSum.of_eq_of_ne, ZeroMemClass, ZeroMemClass.coe_zero, coe_zero, decompose_of_mem, hij.symm, of_eq_of_ne
-/
theorem decompose_of_mem_ne {x : M} {i j : ι} (hx : x in ℳ i) (hij : i != j) :
    (decompose ℳ x j : M) = 0 := by
  rw [decompose_of_mem _ hx]; rw [DirectSum.of_eq_of_ne _ _ _ hij.symm]; rw [ZeroMemClass.coe_zero]

/--
theorem `degree_eq_of_mem_mem` / 定理 `degree_eq_of_mem_mem`

English:
theorem degree_eq_of_mem_mem
  given: {x : M} {i j : ι} (hxi : x in ℳ i) (hxj : x in ℳ j) (hx : x != 0)
  proof: by
  contrapose! hx; rw [← decompose_of_mem_same ℳ hxj, decompose_of_mem_ne ℳ hxi hx]

#adaptation_note

中文:
定理 degree_eq_of_mem_mem
  条件: {x : M} {i j : ι} (hxi : x in ℳ i) (hxj : x in ℳ j) (hx : x != 0)
  证明: by
  contrapose! hx; rw [← decompose_of_mem_same ℳ hxj, decompose_of_mem_ne ℳ hxi hx]

#adaptation_note

Depends on / 依赖: contrapose, decompose_of_mem_ne, decompose_of_mem_same
-/
theorem degree_eq_of_mem_mem {x : M} {i j : ι} (hxi : x in ℳ i) (hxj : x in ℳ j) (hx : x != 0) :
    i = j := by
  contrapose! hx; rw [← decompose_of_mem_same ℳ hxj, decompose_of_mem_ne ℳ hxi hx]

#adaptation_note
/--
`simps!` won't apply `AddEquiv.symm_mk` without the `id <|` in `map_add'`.
`decompose` and `Equiv.symm` are not implicit-reducible, so the type of the proof doesn't match the
expected type up to implicit reducibility. If we remove `id`, we don't get an immediate error,
but some downstream declarations will break.
-/
/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
an additive monoid to a direct sum of components. -/
@[simps!]
/--
Definition of `decomposeAddEquiv` / `decomposeAddEquiv` 的定义

English:
definition decomposeAddEquiv
  signature: : M ≃+ ⨁ i, ℳ i
  body: AddEquiv.symm { (decompose ℳ).symm with
map_add' := id map_add (DirectSum.coeAddMonoidHom ℳ) }

@[simp]

中文:
定义 decomposeAddEquiv
  签名: : M ≃+ ⨁ i, ℳ i
  定义体: AddEquiv.symm { (decompose ℳ).symm with
map_add' := id map_add (DirectSum.coeAddMonoidHom ℳ) }

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.symm, DirectSum, DirectSum.coeAddMonoidHom, coeAddMonoidHom, decompose, map_add
-/
def decomposeAddEquiv : M ≃+ ⨁ i, ℳ i :=
  AddEquiv.symm { (decompose ℳ).symm with
map_add' := id map_add (DirectSum.coeAddMonoidHom ℳ) }

@[simp]
/--
theorem `decompose_zero` / 定理 `decompose_zero`

English:
theorem decompose_zero
  statement: decompose ℳ (0 : M) = 0
  proof: map_zero (decomposeAddEquiv ℳ)

@[simp]

中文:
定理 decompose_zero
  结论: decompose ℳ (0 : M) = 0
  证明: map_zero (decomposeAddEquiv ℳ)

@[simp]

Depends on / 依赖: decomposeAddEquiv, map_zero
-/
theorem decompose_zero : decompose ℳ (0 : M) = 0 :=
  map_zero (decomposeAddEquiv ℳ)

@[simp]
/--
theorem `decompose_symm_zero` / 定理 `decompose_symm_zero`

English:
theorem decompose_symm_zero
  statement: (decompose ℳ).symm 0 = (0 : M)
  proof: map_zero (decomposeAddEquiv ℳ).symm

@[simp]

中文:
定理 decompose_symm_zero
  结论: (decompose ℳ).symm 0 = (0 : M)
  证明: map_zero (decomposeAddEquiv ℳ).symm

@[simp]

Depends on / 依赖: decomposeAddEquiv, map_zero
-/
theorem decompose_symm_zero : (decompose ℳ).symm 0 = (0 : M) :=
  map_zero (decomposeAddEquiv ℳ).symm

@[simp]
/--
theorem `decompose_add` / 定理 `decompose_add`

English:
theorem decompose_add
  given: (x y : M)
  statement: decompose ℳ (x + y) = decompose ℳ x + decompose ℳ y
  proof: map_add (decomposeAddEquiv ℳ) x y

@[simp]

中文:
定理 decompose_add
  条件: (x y : M)
  结论: decompose ℳ (x + y) = decompose ℳ x + decompose ℳ y
  证明: map_add (decomposeAddEquiv ℳ) x y

@[simp]

Depends on / 依赖: decomposeAddEquiv, map_add
-/
theorem decompose_add (x y : M) : decompose ℳ (x + y) = decompose ℳ x + decompose ℳ y :=
  map_add (decomposeAddEquiv ℳ) x y

@[simp]
/--
theorem `decompose_symm_add` / 定理 `decompose_symm_add`

English:
theorem decompose_symm_add
  given: (x y : ⨁ i, ℳ i)
  proof: map_add (decomposeAddEquiv ℳ).symm x y

@[simp]

中文:
定理 decompose_symm_add
  条件: (x y : ⨁ i, ℳ i)
  证明: map_add (decomposeAddEquiv ℳ).symm x y

@[simp]

Depends on / 依赖: decomposeAddEquiv, map_add
-/
theorem decompose_symm_add (x y : ⨁ i, ℳ i) :
    (decompose ℳ).symm (x + y) = (decompose ℳ).symm x + (decompose ℳ).symm y :=
  map_add (decomposeAddEquiv ℳ).symm x y

@[simp]
/--
theorem `decompose_sum` / 定理 `decompose_sum`

English:
theorem decompose_sum
  given: {ι'} (s : Finset ι') (f : ι' -> M)
  proof: map_sum (decomposeAddEquiv ℳ) f s

@[simp]

中文:
定理 decompose_sum
  条件: {ι'} (s : Finset ι') (f : ι' -> M)
  证明: map_sum (decomposeAddEquiv ℳ) f s

@[simp]

Depends on / 依赖: decomposeAddEquiv, map_sum
-/
theorem decompose_sum {ι'} (s : Finset ι') (f : ι' -> M) :
    decompose ℳ (∑ i in s, f i) = ∑ i in s, decompose ℳ (f i) :=
  map_sum (decomposeAddEquiv ℳ) f s

@[simp]
/--
theorem `decompose_symm_sum` / 定理 `decompose_symm_sum`

English:
theorem decompose_symm_sum
  given: {ι'} (s : Finset ι') (f : ι' -> ⨁ i, ℳ i)
  proof: map_sum (decomposeAddEquiv ℳ).symm f s

中文:
定理 decompose_symm_sum
  条件: {ι'} (s : Finset ι') (f : ι' -> ⨁ i, ℳ i)
  证明: map_sum (decomposeAddEquiv ℳ).symm f s

Depends on / 依赖: decomposeAddEquiv, map_sum
-/
theorem decompose_symm_sum {ι'} (s : Finset ι') (f : ι' -> ⨁ i, ℳ i) :
    (decompose ℳ).symm (∑ i in s, f i) = ∑ i in s, (decompose ℳ).symm (f i) :=
  map_sum (decomposeAddEquiv ℳ).symm f s

/--
theorem `sum_support_decompose` / 定理 `sum_support_decompose`

English:
theorem sum_support_decompose
  given: [forall (i) (x : ℳ i), Decidable (x != 0)] (r : M)
  proof: by
  conv_rhs =>
    rw [← (decompose ℳ).symm_apply_apply r]; rw [← sum_support_of (decompose ℳ r)]
  rw [decompose_symm_sum]
  simp_rw [decompose_symm_of]

中文:
定理 sum_support_decompose
  条件: [对任意 (i) (x : ℳ i), Decidable (x != 0)] (r : M)
  证明: by
  conv_rhs =>
    rw [← (decompose ℳ).symm_apply_apply r]; rw [← sum_support_of (decompose ℳ r)]
  rw [decompose_symm_sum]
  simp_rw [decompose_symm_of]

Depends on / 依赖: conv_rhs, decompose, decompose_symm_of, decompose_symm_sum, simp_rw, sum_support_of, symm_apply_apply
-/
theorem sum_support_decompose [forall (i) (x : ℳ i), Decidable (x != 0)] (r : M) :
    (∑ i in (decompose ℳ r).support, (decompose ℳ r i : M)) = r := by
  conv_rhs =>
    rw [← (decompose ℳ).symm_apply_apply r]; rw [← sum_support_of (decompose ℳ r)]
  rw [decompose_symm_sum]
  simp_rw [decompose_symm_of]

/--
theorem `AddSubmonoidClass.IsHomogeneous.mem_iff` / 定理 `AddSubmonoidClass.IsHomogeneous.mem_iff`

English:
theorem AddSubmonoidClass.IsHomogeneous.mem_iff
  proof: by
  classical
  refine ⟨fun hx i => hp i hx, fun hx => ?_⟩
  rw [← DirectSum.sum_support_decompose ℳ x]
  exact sum_mem (fun i _ => hx i)

中文:
定理 AddSubmonoidClass.IsHomogeneous.mem_iff
  证明: by
  classical
  refine ⟨fun hx i => hp i hx, fun hx => ?_⟩
  rw [← DirectSum.sum_support_decompose ℳ x]
  exact sum_mem (fun i _ => hx i)

Depends on / 依赖: DirectSum, DirectSum.sum_support_decompose, classical, sum_mem, sum_support_decompose
-/
theorem AddSubmonoidClass.IsHomogeneous.mem_iff
    {P : Type*} [SetLike P M] [AddSubmonoidClass P M] (p : P)
    (hp : SetLike.IsHomogeneous ℳ p) {x} :
    x in p ↔ forall i, (decompose ℳ x i : M) in p := by
  classical
  refine ⟨fun hx i => hp i hx, fun hx => ?_⟩
  rw [← DirectSum.sum_support_decompose ℳ x]
  exact sum_mem (fun i _ => hx i)

/--
theorem `AddSubmonoidClass.IsHomogeneous.ext` / 定理 `AddSubmonoidClass.IsHomogeneous.ext`

English:
theorem AddSubmonoidClass.IsHomogeneous.ext
  proof: by
  refine SetLike.ext fun m => ?_
  rw [AddSubmonoidClass.IsHomogeneous.mem_iff ℳ p hp]; rw [AddSubmonoidClass.IsHomogeneous.mem_iff ℳ q hq]
  exact forall_congr' fun i => hpq i _ (decompose ℳ _ i).2

中文:
定理 AddSubmonoidClass.IsHomogeneous.ext
  证明: by
  refine SetLike.ext fun m => ?_
  rw [AddSubmonoidClass.IsHomogeneous.mem_iff ℳ p hp]; rw [AddSubmonoidClass.IsHomogeneous.mem_iff ℳ q hq]
  exact forall_congr' fun i => hpq i _ (decompose ℳ _ i).2

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.IsHomogeneous.mem_iff, IsHomogeneous, SetLike, SetLike.ext, decompose, forall_congr, mem_iff
-/
theorem AddSubmonoidClass.IsHomogeneous.ext
    {ℳ : ι -> σ} [Decomposition ℳ] {P : Type*} [SetLike P M] [AddSubmonoidClass P M]
    {p q : P} (hp : SetLike.IsHomogeneous ℳ p) (hq : SetLike.IsHomogeneous ℳ q)
    (hpq : forall i, forall m in ℳ i, m in p ↔ m in q) :
    p = q := by
  refine SetLike.ext fun m => ?_
  rw [AddSubmonoidClass.IsHomogeneous.mem_iff ℳ p hp]; rw [AddSubmonoidClass.IsHomogeneous.mem_iff ℳ q hq]
  exact forall_congr' fun i => hpq i _ (decompose ℳ _ i).2

end AddCommMonoid

section AddCommGroup

variable [DecidableEq ι] [AddCommGroup M]
variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι -> σ)
variable [Decomposition ℳ]

@[simp]
/--
theorem `decompose_neg` / 定理 `decompose_neg`

English:
theorem decompose_neg
  given: (x : M)
  statement: decompose ℳ (-x) = -decompose ℳ x
  proof: map_neg (decomposeAddEquiv ℳ) x

@[simp]

中文:
定理 decompose_neg
  条件: (x : M)
  结论: decompose ℳ (-x) = -decompose ℳ x
  证明: map_neg (decomposeAddEquiv ℳ) x

@[simp]

Depends on / 依赖: decomposeAddEquiv, map_neg
-/
theorem decompose_neg (x : M) : decompose ℳ (-x) = -decompose ℳ x :=
  map_neg (decomposeAddEquiv ℳ) x

@[simp]
/--
theorem `decompose_symm_neg` / 定理 `decompose_symm_neg`

English:
theorem decompose_symm_neg
  given: (x : ⨁ i, ℳ i)
  statement: (decompose ℳ).symm (-x) = -(decompose ℳ).symm x
  proof: map_neg (decomposeAddEquiv ℳ).symm x

@[simp]

中文:
定理 decompose_symm_neg
  条件: (x : ⨁ i, ℳ i)
  结论: (decompose ℳ).symm (-x) = -(decompose ℳ).symm x
  证明: map_neg (decomposeAddEquiv ℳ).symm x

@[simp]

Depends on / 依赖: decomposeAddEquiv, map_neg
-/
theorem decompose_symm_neg (x : ⨁ i, ℳ i) : (decompose ℳ).symm (-x) = -(decompose ℳ).symm x :=
  map_neg (decomposeAddEquiv ℳ).symm x

@[simp]
/--
theorem `decompose_sub` / 定理 `decompose_sub`

English:
theorem decompose_sub
  given: (x y : M)
  statement: decompose ℳ (x - y) = decompose ℳ x - decompose ℳ y
  proof: map_sub (decomposeAddEquiv ℳ) x y

@[simp]

中文:
定理 decompose_sub
  条件: (x y : M)
  结论: decompose ℳ (x - y) = decompose ℳ x - decompose ℳ y
  证明: map_sub (decomposeAddEquiv ℳ) x y

@[simp]

Depends on / 依赖: decomposeAddEquiv, map_sub
-/
theorem decompose_sub (x y : M) : decompose ℳ (x - y) = decompose ℳ x - decompose ℳ y :=
  map_sub (decomposeAddEquiv ℳ) x y

@[simp]
/--
theorem `decompose_symm_sub` / 定理 `decompose_symm_sub`

English:
theorem decompose_symm_sub
  given: (x y : ⨁ i, ℳ i)
  proof: map_sub (decomposeAddEquiv ℳ).symm x y

中文:
定理 decompose_symm_sub
  条件: (x y : ⨁ i, ℳ i)
  证明: map_sub (decomposeAddEquiv ℳ).symm x y

Depends on / 依赖: decomposeAddEquiv, map_sub
-/
theorem decompose_symm_sub (x y : ⨁ i, ℳ i) :
    (decompose ℳ).symm (x - y) = (decompose ℳ).symm x - (decompose ℳ).symm y :=
  map_sub (decomposeAddEquiv ℳ).symm x y

end AddCommGroup

section Module

variable [DecidableEq ι] [Semiring R] [AddCommMonoid M] [Module R M]
variable (ℳ : ι -> Submodule R M)

/--
Definition of `Decomposition.ofLinearMap` / `Decomposition.ofLinearMap` 的定义

English:
abbreviation Decomposition.ofLinearMap
  signature: (decompose : M ->ₗ[R] ⨁ i, ℳ i)
  body: decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv

中文:
缩写 Decomposition.ofLinearMap
  签名: (decompose : M ->ₗ[R] ⨁ i, ℳ i)
  定义体: decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv

Depends on / 依赖: decompose
-/
abbrev Decomposition.ofLinearMap (decompose : M ->ₗ[R] ⨁ i, ℳ i)
    (h_left_inv : DirectSum.coeLinearMap ℳ ∘ₗ decompose = .id)
    (h_right_inv : decompose ∘ₗ DirectSum.coeLinearMap ℳ = .id) : Decomposition ℳ where
  decompose' := decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv

variable [Decomposition ℳ]

/--
Definition of `decomposeLinearEquiv` / `decomposeLinearEquiv` 的定义

English:
definition decomposeLinearEquiv
  signature: : M ≃ₗ[R] ⨁ i, ℳ i
  body: LinearEquiv.symm
    { (decomposeAddEquiv ℳ).symm with map_smul' := map_smul (DirectSum.coeLinearMap ℳ) }

中文:
定义 decomposeLinearEquiv
  签名: : M ≃ₗ[R] ⨁ i, ℳ i
  定义体: LinearEquiv.symm
    { (decomposeAddEquiv ℳ).symm with map_smul' := map_smul (DirectSum.coeLinearMap ℳ) }

Depends on / 依赖: DirectSum, DirectSum.coeLinearMap, LinearEquiv, LinearEquiv.symm, coeLinearMap, decomposeAddEquiv, map_smul
-/
def decomposeLinearEquiv : M ≃ₗ[R] ⨁ i, ℳ i :=
  LinearEquiv.symm
    { (decomposeAddEquiv ℳ).symm with map_smul' := map_smul (DirectSum.coeLinearMap ℳ) }

/--
theorem `decomposeLinearEquiv_apply` / 定理 `decomposeLinearEquiv_apply`

English:
theorem decomposeLinearEquiv_apply
  given: (m : M)
  proof: rfl

中文:
定理 decomposeLinearEquiv_apply
  条件: (m : M)
  证明: rfl
-/
theorem decomposeLinearEquiv_apply (m : M) :
    decomposeLinearEquiv ℳ m = decompose ℳ m := rfl

/--
theorem `decomposeLinearEquiv_symm_apply` / 定理 `decomposeLinearEquiv_symm_apply`

English:
theorem decomposeLinearEquiv_symm_apply
  given: (m : ⨁ i, ℳ i)
  proof: rfl

@[simp]

中文:
定理 decomposeLinearEquiv_symm_apply
  条件: (m : ⨁ i, ℳ i)
  证明: rfl

@[simp]
-/
theorem decomposeLinearEquiv_symm_apply (m : ⨁ i, ℳ i) :
    (decomposeLinearEquiv ℳ).symm m = (decompose ℳ).symm m := rfl

@[simp]
/--
theorem `decompose_smul` / 定理 `decompose_smul`

English:
theorem decompose_smul
  given: (r : R) (x : M)
  statement: decompose ℳ (r • x) = r • decompose ℳ x
  proof: map_smul (decomposeLinearEquiv ℳ) r x

中文:
定理 decompose_smul
  条件: (r : R) (x : M)
  结论: decompose ℳ (r • x) = r • decompose ℳ x
  证明: map_smul (decomposeLinearEquiv ℳ) r x

Depends on / 依赖: decomposeLinearEquiv, map_smul
-/
theorem decompose_smul (r : R) (x : M) : decompose ℳ (r • x) = r • decompose ℳ x :=
  map_smul (decomposeLinearEquiv ℳ) r x

/--
theorem `decomposeLinearEquiv_symm_comp_lof` / 定理 `decomposeLinearEquiv_symm_comp_lof`

English:
theorem decomposeLinearEquiv_symm_comp_lof
  given: (i : ι)
  proof: LinearMap.ext decompose_symm_of _

中文:
定理 decomposeLinearEquiv_symm_comp_lof
  条件: (i : ι)
  证明: LinearMap.ext decompose_symm_of _
-/
@[simp] theorem decomposeLinearEquiv_symm_comp_lof (i : ι) :
    (decomposeLinearEquiv ℳ).symm ∘ₗ lof R ι (ℳ ·) i = (ℳ i).subtype :=
LinearMap.ext decompose_symm_of _

/--
lemma `decomposeLinearEquiv_symm_lof` / 引理 `decomposeLinearEquiv_symm_lof`

English:
lemma decomposeLinearEquiv_symm_lof
  given: (i : ι) (x : ℳ i)
  proof: congr($(decomposeLinearEquiv_symm_comp_lof ℳ i) x)

中文:
引理 decomposeLinearEquiv_symm_lof
  条件: (i : ι) (x : ℳ i)
  证明: congr($(decomposeLinearEquiv_symm_comp_lof ℳ i) x)
-/
@[simp] lemma decomposeLinearEquiv_symm_lof (i : ι) (x : ℳ i) :
    (decomposeLinearEquiv ℳ).symm (lof R _ _ i x) = x :=
  congr($(decomposeLinearEquiv_symm_comp_lof ℳ i) x)

/--
lemma `decomposeLinearEquiv_apply_coe` / 引理 `decomposeLinearEquiv_apply_coe`

English:
lemma decomposeLinearEquiv_apply_coe
  given: (i : ι) (x : ℳ i)
  proof: (LinearEquiv.eq_symm_apply _).mp (decomposeLinearEquiv_symm_lof ..).symm

中文:
引理 decomposeLinearEquiv_apply_coe
  条件: (i : ι) (x : ℳ i)
  证明: (LinearEquiv.eq_symm_apply _).mp (decomposeLinearEquiv_symm_lof ..).symm
-/
@[simp] lemma decomposeLinearEquiv_apply_coe (i : ι) (x : ℳ i) :
    decomposeLinearEquiv ℳ x = lof R _ _ i x :=
  (LinearEquiv.eq_symm_apply _).mp (decomposeLinearEquiv_symm_lof ..).symm

/--
theorem `decompose_lhom_ext` / 定理 `decompose_lhom_ext`

English:
theorem decompose_lhom_ext
  given: {N} [AddCommMonoid N] [Module R N] ⦃f g
  statement: M ->ₗ[R] N⦄
  proof: LinearMap.ext (decomposeLinearEquiv ℳ).symm.surjective.forall.mpr
    suffices f ∘ₗ (decomposeLinearEquiv ℳ).symm
           = (g ∘ₗ (decomposeLinearEquiv ℳ).symm : (⨁ i, ℳ i) ->ₗ[R] N) from
      DFunLike.congr_fun this
    linearMap_ext _ fun i => by
      simp_rw [LinearMap.comp_assoc, decomposeL

中文:
定理 decompose_lhom_ext
  条件: {N} [AddCommMonoid N] [Module R N] ⦃f g
  结论: M ->ₗ[R] N⦄
  证明: LinearMap.ext (decomposeLinearEquiv ℳ).symm.surjective.forall.mpr
    suffices f ∘ₗ (decomposeLinearEquiv ℳ).symm
           = (g ∘ₗ (decomposeLinearEquiv ℳ).symm : (⨁ i, ℳ i) ->ₗ[R] N) from
      DFunLike.congr_fun this
    linearMap_ext _ fun i => by
      simp_rw [LinearMap.comp_assoc, decomposeL

Depends on / 依赖: DFunLike, DFunLike.congr_fun, LinearMap, LinearMap.comp_assoc, LinearMap.ext, comp_assoc, congr_fun, decomposeLinearEquiv, decomposeLinearEquiv_symm_comp_lof, linearMap_ext, simp_rw, surjective, symm.surjective.forall.mpr
-/
theorem decompose_lhom_ext {N} [AddCommMonoid N] [Module R N] ⦃f g : M ->ₗ[R] N⦄
    (h : forall i, f ∘ₗ (ℳ i).subtype = g ∘ₗ (ℳ i).subtype) : f = g :=
LinearMap.ext (decomposeLinearEquiv ℳ).symm.surjective.forall.mpr
    suffices f ∘ₗ (decomposeLinearEquiv ℳ).symm
           = (g ∘ₗ (decomposeLinearEquiv ℳ).symm : (⨁ i, ℳ i) ->ₗ[R] N) from
      DFunLike.congr_fun this
    linearMap_ext _ fun i => by
      simp_rw [LinearMap.comp_assoc, decomposeLinearEquiv_symm_comp_lof ℳ i, h]

end Module

end DirectSum
