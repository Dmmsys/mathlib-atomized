/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Zhangir Azerbayev
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basis


/-!
# Alternating Maps

We construct the bundled function `AlternatingMap`, which extends `MultilinearMap` with all the
arguments of the same type.

## Main definitions
* `AlternatingMap R M N ι` is the space of `R`-linear alternating maps from `ι → M` to `N`.
* `f.map_eq_zero_of_eq` expresses that `f` is zero when two inputs are equal.
* `f.map_swap` expresses that `f` is negated when two inputs are swapped.
* `f.map_perm` expresses how `f` varies by a sign change under a permutation of its inputs.
* An `AddCommMonoid`, `AddCommGroup`, and `Module` structure over `AlternatingMap`s that
  matches the definitions over `MultilinearMap`s.
* `AlternatingMap.domDomCongr`, for permuting the elements within a family.
* `MultilinearMap.alternatization`, which makes an alternating map out of a non-alternating one.
* `AlternatingMap.curryLeft`, for binding the leftmost argument of an alternating map indexed
  by `Fin n.succ`.

## Implementation notes
`AlternatingMap` is defined in terms of `map_eq_zero_of_eq`, as this is easier to work with than
using `map_swap` as a definition, and does not require `Neg N`.

`AlternatingMap`s are provided with a coercion to `MultilinearMap`, along with a set of
`norm_cast` lemmas that act on the algebraic structure:

* `AlternatingMap.coe_add`
* `AlternatingMap.coe_zero`
* `AlternatingMap.coe_sub`
* `AlternatingMap.coe_neg`
* `AlternatingMap.coe_smul`
-/

@[expose] public section

open Module

-- semiring / add_comm_monoid

variable {R : Type*} [Semiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {P : Type*} [AddCommMonoid P] [Module R P]

-- semiring / add_comm_group

variable {M' : Type*} [AddCommGroup M'] [Module R M']
variable {N' : Type*} [AddCommGroup N'] [Module R N']
variable {ι ι' ι'' : Type*}

section

variable (R M N ι)

/--
Definition of `AlternatingMap` / `AlternatingMap` 的定义

English:
structure AlternatingMap
  parameters: extends MultilinearMap R (fun _ : ι => M) N
  extends: MultilinearMap R (fun _ : ι => M) N
  axioms and operations (1):
    - map_eq_zero_of_eq' : forall (v : ι -> M) (i j : ι), v i = v j -> i != j -> toFun v = 0

中文:
结构 交错映射
  参数: extends 多重线性映射 R (fun _ : ι => M) N
  继承: 多重线性映射 R (fun _ : ι => M) N
  公理与运算 (1 个):
    - map_eq_zero_of_eq' : 对任意 (v : ι -> M) (i j : ι), v i = v j -> i != j -> toFun v = 0
-/
structure AlternatingMap extends MultilinearMap R (fun _ : ι => M) N where
  /-- The map is alternating: if `v` has two equal coordinates, then `f v = 0`. -/
  map_eq_zero_of_eq' : forall (v : ι -> M) (i j : ι), v i = v j -> i != j -> toFun v = 0

@[inherit_doc]
notation M " [⋀^" ι "]->ₗ[" R "] " N:100 => AlternatingMap R M N ι

end

/-- The multilinear map associated to an alternating map -/
add_decl_doc AlternatingMap.toMultilinearMap

namespace AlternatingMap

variable (f f' : M [⋀^ι]->ₗ[R] N)
variable (g g₂ : M [⋀^ι]->ₗ[R] N')
variable (g' : M' [⋀^ι]->ₗ[R] N')
variable (v : ι -> M) (v' : ι -> M')

open Function

/-! Basic coercion simp lemmas, largely copied from `RingHom` and `MultilinearMap` -/


section Coercions

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (M [⋀^ι]->ₗ[R] N) (ι -> M) N where
  body: f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨_, _, _⟩, _⟩
    rcases g with ⟨⟨_, _, _⟩, _⟩
    congr

initialize_simps_projections AlternatingMap (toFun -> apply)

@[simp]

中文:
实例 instFunLike
  签名: : 函数状 (M [⋀^ι]->ₗ[R] N) (ι -> M) N where
  定义体: f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨_, _, _⟩, _⟩
    rcases g with ⟨⟨_, _, _⟩, _⟩
    congr

initialize_simps_projections AlternatingMap (toFun -> apply)

@[simp]

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (M [⋀^ι]->ₗ[R] N) (ι -> M) N where
  coe f := f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨_, _, _⟩, _⟩
    rcases g with ⟨⟨_, _, _⟩, _⟩
    congr

initialize_simps_projections AlternatingMap (toFun -> apply)

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  statement: f.toFun = f
  proof: rfl

@[simp]

中文:
定理 toFun_eq_coe
  结论: f.toFun = f
  证明: rfl

@[simp]
-/
theorem toFun_eq_coe : f.toFun = f :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : MultilinearMap R (fun _ : ι => M) N) (h)
  proof: rfl

中文:
定理 coe_mk
  条件: (f : 多重线性映射 R (fun _ : ι => M) N) (h)
  证明: rfl
-/
theorem coe_mk (f : MultilinearMap R (fun _ : ι => M) N) (h) :
    ⇑(⟨f, h⟩ : M [⋀^ι]->ₗ[R] N) = f :=
  rfl

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : M [⋀^ι]->ₗ[R] N} (h : f = g) (x : ι -> M)
  statement: f x = g x
  proof: congr_arg (fun h : M [⋀^ι]->ₗ[R] N => h x) h

中文:
定理 congr_fun
  条件: {f g : M [⋀^ι]->ₗ[R] N} (h : f = g) (x : ι -> M)
  结论: f x = g x
  证明: congr_arg (fun h : M [⋀^ι]->ₗ[R] N => h x) h
-/
protected theorem congr_fun {f g : M [⋀^ι]->ₗ[R] N} (h : f = g) (x : ι -> M) : f x = g x :=
  congr_arg (fun h : M [⋀^ι]->ₗ[R] N => h x) h

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: (f : M [⋀^ι]->ₗ[R] N) {x y : ι -> M} (h : x = y)
  statement: f x = f y
  proof: congr_arg (fun x : ι -> M => f x) h

中文:
定理 congr_arg
  条件: (f : M [⋀^ι]->ₗ[R] N) {x y : ι -> M} (h : x = y)
  结论: f x = f y
  证明: congr_arg (fun x : ι -> M => f x) h
-/
protected theorem congr_arg (f : M [⋀^ι]->ₗ[R] N) {x y : ι -> M} (h : x = y) : f x = f y :=
  congr_arg (fun x : ι -> M => f x) h

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective ((↑) : M [⋀^ι]->ₗ[R] N -> (ι -> M) -> N)
  proof: DFunLike.coe_injective

@[norm_cast]

中文:
定理 coe_injective
  结论: 单射 ((↑) : M [⋀^ι]->ₗ[R] N -> (ι -> M) -> N)
  证明: DFunLike.coe_injective

@[norm_cast]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective : Injective ((↑) : M [⋀^ι]->ₗ[R] N -> (ι -> M) -> N) :=
  DFunLike.coe_injective

@[norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {f g : M [⋀^ι]->ₗ[R] N}
  statement: (f : (ι -> M) -> N) = g ↔ f = g
  proof: coe_injective.eq_iff

@[ext]

中文:
定理 coe_inj
  条件: {f g : M [⋀^ι]->ₗ[R] N}
  结论: (f : (ι -> M) -> N) = g ↔ f = g
  证明: coe_injective.eq_iff

@[ext]

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff
-/
theorem coe_inj {f g : M [⋀^ι]->ₗ[R] N} : (f : (ι -> M) -> N) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f' x)
  statement: f = f'
  proof: DFunLike.ext _ _ H

中文:
定理 ext
  条件: {f f' : M [⋀^ι]->ₗ[R] N} (H : 对任意 x, f x = f' x)
  结论: f = f'
  证明: DFunLike.ext _ _ H

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ H

attribute [coe] AlternatingMap.toMultilinearMap

/--
Instance `instCoe` / 实例 `instCoe`

English:
instance instCoe
  signature: : Coe (M [⋀^ι]->ₗ[R] N) (MultilinearMap R (fun _ : ι => M) N)
  body: ⟨fun x => x.toMultilinearMap⟩

@[simp, norm_cast]

中文:
实例 instCoe
  签名: : Coe (M [⋀^ι]->ₗ[R] N) (多重线性映射 R (fun _ : ι => M) N)
  定义体: ⟨fun x => x.toMultilinearMap⟩

@[simp, norm_cast]

Depends on / 依赖: toMultilinearMap, x.toMultilinearMap
-/
instance instCoe : Coe (M [⋀^ι]->ₗ[R] N) (MultilinearMap R (fun _ : ι => M) N) :=
  ⟨fun x => x.toMultilinearMap⟩

@[simp, norm_cast]
/--
theorem `coe_multilinearMap` / 定理 `coe_multilinearMap`

English:
theorem coe_multilinearMap
  statement: ⇑(f : MultilinearMap R (fun _ : ι => M) N) = f
  proof: rfl

中文:
定理 coe_multilinearMap
  结论: ⇑(f : 多重线性映射 R (fun _ : ι => M) N) = f
  证明: rfl
-/
theorem coe_multilinearMap : ⇑(f : MultilinearMap R (fun _ : ι => M) N) = f :=
  rfl

/--
theorem `coe_multilinearMap_injective` / 定理 `coe_multilinearMap_injective`

English:
theorem coe_multilinearMap_injective
  proof: fun _ _ h => ext MultilinearMap.congr_fun h

中文:
定理 coe_multilinearMap_injective
  证明: fun _ _ h => ext MultilinearMap.congr_fun h

Depends on / 依赖: MultilinearMap, MultilinearMap.congr_fun, congr_fun
-/
theorem coe_multilinearMap_injective :
    Function.Injective ((↑) : M [⋀^ι]->ₗ[R] N -> MultilinearMap R (fun _ : ι => M) N) :=
fun _ _ h => ext MultilinearMap.congr_fun h

/--
theorem `coe_multilinearMap_mk` / 定理 `coe_multilinearMap_mk`

English:
theorem coe_multilinearMap_mk
  given: (f : (ι -> M) -> N) (h₁ h₂ h₃)
  proof: by
  simp

中文:
定理 coe_multilinearMap_mk
  条件: (f : (ι -> M) -> N) (h₁ h₂ h₃)
  证明: by
  simp
-/
theorem coe_multilinearMap_mk (f : (ι -> M) -> N) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁, h₂⟩, h₃⟩ : M [⋀^ι]->ₗ[R] N) : MultilinearMap R (fun _ : ι => M) N) =
      ⟨f, @h₁, @h₂⟩ := by
  simp

end Coercions

/-!
### Simp-normal forms of the structure fields

These are expressed in terms of `⇑f` instead of `f.toFun`.
-/


@[simp]
/--
theorem `map_update_add` / 定理 `map_update_add`

English:
theorem map_update_add
  given: [DecidableEq ι] (i : ι) (x y : M)
  proof: f.map_update_add' v i x y

@[simp]

中文:
定理 map_update_add
  条件: [DecidableEq ι] (i : ι) (x y : M)
  证明: f.map_update_add' v i x y

@[simp]

Depends on / 依赖: ContinuousSup, ContinuousSup.measurableSup, f.map_update_add, map_update_add, measurableSup
-/
theorem map_update_add [DecidableEq ι] (i : ι) (x y : M) :
    f (update v i (x + y)) = f (update v i x) + f (update v i y) :=
  f.map_update_add' v i x y

@[simp]
/--
theorem `map_update_sub` / 定理 `map_update_sub`

English:
theorem map_update_sub
  given: [DecidableEq ι] (i : ι) (x y : M')
  proof: g'.toMultilinearMap.map_update_sub v' i x y

@[simp]

中文:
定理 map_update_sub
  条件: [DecidableEq ι] (i : ι) (x y : M')
  证明: g'.toMultilinearMap.map_update_sub v' i x y

@[simp]

Depends on / 依赖: ContinuousSup, ContinuousSup.measurableSup, SecondCountableTopology, map_update_sub, toMultilinearMap, toMultilinearMap.map_update_sub
-/
theorem map_update_sub [DecidableEq ι] (i : ι) (x y : M') :
    g' (update v' i (x - y)) = g' (update v' i x) - g' (update v' i y) :=
  g'.toMultilinearMap.map_update_sub v' i x y

@[simp]
/--
theorem `map_update_neg` / 定理 `map_update_neg`

English:
theorem map_update_neg
  given: [DecidableEq ι] (i : ι) (x : M')
  proof: g'.toMultilinearMap.map_update_neg v' i x

@[simp]

中文:
定理 map_update_neg
  条件: [DecidableEq ι] (i : ι) (x : M')
  证明: g'.toMultilinearMap.map_update_neg v' i x

@[simp]

Depends on / 依赖: ContinuousInf, ContinuousInf.measurableInf, map_update_neg, measurableInf, toMultilinearMap, toMultilinearMap.map_update_neg
-/
theorem map_update_neg [DecidableEq ι] (i : ι) (x : M') :
    g' (update v' i (-x)) = -g' (update v' i x) :=
  g'.toMultilinearMap.map_update_neg v' i x

@[simp]
/--
theorem `map_update_smul` / 定理 `map_update_smul`

English:
theorem map_update_smul
  given: [DecidableEq ι] (i : ι) (r : R) (x : M)
  proof: f.map_update_smul' v i r x

中文:
定理 map_update_smul
  条件: [DecidableEq ι] (i : ι) (r : R) (x : M)
  证明: f.map_update_smul' v i r x

Depends on / 依赖: ContinuousInf, ContinuousInf.measurableInf, SecondCountableTopology, f.map_update_smul, map_update_smul
-/
theorem map_update_smul [DecidableEq ι] (i : ι) (r : R) (x : M) :
    f (update v i (r • x)) = r • f (update v i x) :=
  f.map_update_smul' v i r x

-- Cannot be @[simp] because `i` and `j` cannot be inferred by `simp`.
/--
theorem `map_eq_zero_of_eq` / 定理 `map_eq_zero_of_eq`

English:
theorem map_eq_zero_of_eq
  given: (v : ι -> M) {i j : ι} (h : v i = v j) (hij : i != j)
  statement: f v = 0
  proof: f.map_eq_zero_of_eq' v i j h hij

中文:
定理 map_eq_zero_of_eq
  条件: (v : ι -> M) {i j : ι} (h : v i = v j) (hij : i != j)
  结论: f v = 0
  证明: f.map_eq_zero_of_eq' v i j h hij

Depends on / 依赖: f.map_eq_zero_of_eq, map_eq_zero_of_eq
-/
theorem map_eq_zero_of_eq (v : ι -> M) {i j : ι} (h : v i = v j) (hij : i != j) : f v = 0 :=
  f.map_eq_zero_of_eq' v i j h hij

/--
theorem `map_coord_zero` / 定理 `map_coord_zero`

English:
theorem map_coord_zero
  given: {m : ι -> M} (i : ι) (h : m i = 0)
  statement: f m = 0
  proof: f.toMultilinearMap.map_coord_zero i h

@[simp]

中文:
定理 map_coord_zero
  条件: {m : ι -> M} (i : ι) (h : m i = 0)
  结论: f m = 0
  证明: f.toMultilinearMap.map_coord_zero i h

@[simp]

Depends on / 依赖: f.toMultilinearMap.map_coord_zero, map_coord_zero, toMultilinearMap
-/
theorem map_coord_zero {m : ι -> M} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h

@[simp]
/--
theorem `map_update_zero` / 定理 `map_update_zero`

English:
theorem map_update_zero
  given: [DecidableEq ι] (m : ι -> M) (i : ι)
  statement: f (update m i 0) = 0
  proof: f.toMultilinearMap.map_update_zero m i

@[simp]

中文:
定理 map_update_zero
  条件: [DecidableEq ι] (m : ι -> M) (i : ι)
  结论: f (update m i 0) = 0
  证明: f.toMultilinearMap.map_update_zero m i

@[simp]

Depends on / 依赖: f.toMultilinearMap.map_update_zero, map_update_zero, toMultilinearMap
-/
theorem map_update_zero [DecidableEq ι] (m : ι -> M) (i : ι) : f (update m i 0) = 0 :=
  f.toMultilinearMap.map_update_zero m i

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: [Nonempty ι]
  statement: f 0 = 0
  proof: f.toMultilinearMap.map_zero

中文:
定理 map_zero
  条件: [非空 ι]
  结论: f 0 = 0
  证明: f.toMultilinearMap.map_zero

Depends on / 依赖: f.toMultilinearMap.map_zero, map_zero, toMultilinearMap
-/
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero

/--
theorem `map_eq_zero_of_not_injective` / 定理 `map_eq_zero_of_not_injective`

English:
theorem map_eq_zero_of_not_injective
  given: (v : ι -> M) (hv : ¬Function.Injective v)
  statement: f v = 0
  proof: by
  rw [Function.Injective] at hv
  push Not at hv
  rcases hv with ⟨i₁, i₂, heq, hne⟩
  exact f.map_eq_zero_of_eq v heq hne

中文:
定理 map_eq_zero_of_not_injective
  条件: (v : ι -> M) (hv : ¬函数.单射 v)
  结论: f v = 0
  证明: by
  rw [Function.Injective] at hv
  push Not at hv
  rcases hv with ⟨i₁, i₂, heq, hne⟩
  exact f.map_eq_zero_of_eq v heq hne

Depends on / 依赖: Function, Function.Injective, Injective, f.map_eq_zero_of_eq, map_eq_zero_of_eq
-/
theorem map_eq_zero_of_not_injective (v : ι -> M) (hv : ¬Function.Injective v) : f v = 0 := by
  rw [Function.Injective] at hv
  push Not at hv
  rcases hv with ⟨i₁, i₂, heq, hne⟩
  exact f.map_eq_zero_of_eq v heq hne

/-!
### Algebraic structure inherited from `MultilinearMap`

`AlternatingMap` carries the same `AddCommMonoid`, `AddCommGroup`, and `Module` structure
as `MultilinearMap`
-/


section SMul

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul S (M [⋀^ι]->ₗ[R] N)
  body: ⟨fun c f =>
    { c • (f : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩

@[simp]

中文:
实例 instSMul
  签名: : 标量乘法 S (M [⋀^ι]->ₗ[R] N)
  定义体: ⟨fun c f =>
    { c • (f : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩

@[simp]

Depends on / 依赖: MultilinearMap, f.map_eq_zero_of_eq, map_eq_zero_of_eq
-/
instance instSMul : SMul S (M [⋀^ι]->ₗ[R] N) :=
  ⟨fun c f =>
    { c • (f : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩

@[simp]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (c : S) (m : ι -> M)
  statement: (c • f) m = c • f m
  proof: rfl

@[norm_cast]

中文:
定理 smul_apply
  条件: (c : S) (m : ι -> M)
  结论: (c • f) m = c • f m
  证明: rfl

@[norm_cast]
-/
theorem smul_apply (c : S) (m : ι -> M) : (c • f) m = c • f m :=
  rfl

@[norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (c : S)
  statement: ↑(c • f) = c • (f : MultilinearMap R (fun _ : ι => M) N)
  proof: rfl

中文:
定理 coe_smul
  条件: (c : S)
  结论: ↑(c • f) = c • (f : 多重线性映射 R (fun _ : ι => M) N)
  证明: rfl
-/
theorem coe_smul (c : S) : ↑(c • f) = c • (f : MultilinearMap R (fun _ : ι => M) N) :=
  rfl

/--
theorem `coeFn_smul` / 定理 `coeFn_smul`

English:
theorem coeFn_smul
  given: (c : S) (f : M [⋀^ι]->ₗ[R] N)
  statement: ⇑(c • f) = c • ⇑f
  proof: rfl

中文:
定理 coeFn_smul
  条件: (c : S) (f : M [⋀^ι]->ₗ[R] N)
  结论: ⇑(c • f) = c • ⇑f
  证明: rfl
-/
theorem coeFn_smul (c : S) (f : M [⋀^ι]->ₗ[R] N) : ⇑(c • f) = c • ⇑f :=
  rfl

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: {T : Type*} [Monoid T] [DistribMulAction T N] [SMulCommClass R T N]
  body: ext fun _ => smul_comm ..

中文:
实例 instSMulCommClass
  签名: {T : 类型} [幺半群 T] [分配乘法作用 T N] [标量交换类 R T N]
  定义体: ext fun _ => smul_comm ..

Depends on / 依赖: smul_comm
-/
instance instSMulCommClass {T : Type*} [Monoid T] [DistribMulAction T N] [SMulCommClass R T N]
    [SMulCommClass S T N] : SMulCommClass S T (M [⋀^ι]->ₗ[R] N) where
  smul_comm _ _ _ := ext fun _ => smul_comm ..

/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: [DistribMulAction Sᵐᵒᵖ N] [IsCentralScalar S N]
  body: ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

中文:
实例 instIsCentralScalar
  签名: [分配乘法作用 Sᵐᵒᵖ N] [中心标量 S N]
  定义体: ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

Depends on / 依赖: op_smul_eq_smul
-/
instance instIsCentralScalar [DistribMulAction Sᵐᵒᵖ N] [IsCentralScalar S N] :
    IsCentralScalar S (M [⋀^ι]->ₗ[R] N) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

end SMul

/-- The Cartesian product of two alternating maps, as an alternating map. -/
@[simps!]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : M [⋀^ι]->ₗ[R] N) (g : M [⋀^ι]->ₗ[R] P)
  body: { f.toMultilinearMap.prod g.toMultilinearMap with
    map_eq_zero_of_eq' := fun _ _ _ h hne =>
      Prod.ext (f.map_eq_zero_of_eq _ h hne) (g.map_eq_zero_of_eq _ h hne) }

@[simp]

中文:
定义 乘积
  签名: (f : M [⋀^ι]->ₗ[R] N) (g : M [⋀^ι]->ₗ[R] P)
  定义体: { f.toMultilinearMap.prod g.toMultilinearMap with
    map_eq_zero_of_eq' := fun _ _ _ h hne =>
      Prod.ext (f.map_eq_zero_of_eq _ h hne) (g.map_eq_zero_of_eq _ h hne) }

@[simp]

Depends on / 依赖: Prod.ext, f.map_eq_zero_of_eq, f.toMultilinearMap.prod, g.map_eq_zero_of_eq, g.toMultilinearMap, map_eq_zero_of_eq, toMultilinearMap
-/
def prod (f : M [⋀^ι]->ₗ[R] N) (g : M [⋀^ι]->ₗ[R] P) : M [⋀^ι]->ₗ[R] (N × P) :=
  { f.toMultilinearMap.prod g.toMultilinearMap with
    map_eq_zero_of_eq' := fun _ _ _ h hne =>
      Prod.ext (f.map_eq_zero_of_eq _ h hne) (g.map_eq_zero_of_eq _ h hne) }

@[simp]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (f : M [⋀^ι]->ₗ[R] N) (g : M [⋀^ι]->ₗ[R] P)
  proof: rfl

中文:
定理 coe_prod
  条件: (f : M [⋀^ι]->ₗ[R] N) (g : M [⋀^ι]->ₗ[R] P)
  证明: rfl
-/
theorem coe_prod (f : M [⋀^ι]->ₗ[R] N) (g : M [⋀^ι]->ₗ[R] P) :
    (f.prod g : MultilinearMap R (fun _ : ι => M) (N × P)) = MultilinearMap.prod f g :=
  rfl

/-- Combine a family of alternating maps with the same domain and codomains `N i` into an
alternating map taking values in the space of functions `Π i, N i`. -/
@[simps!]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: {ι' : Type*} {N : ι' -> Type*} [forall i, AddCommMonoid (N i)] [forall i, Module R (N i)]
  body: { MultilinearMap.pi fun a => (f a).toMultilinearMap with
    map_eq_zero_of_eq' := fun _ _ _ h hne => funext fun a => (f a).map_eq_zero_of_eq _ h hne }

@[simp]

中文:
定义 pi
  签名: {ι' : 类型} {N : ι' -> 类型} [对任意 i, 加法交换幺半群 (N i)] [对任意 i, 模 R (N i)]
  定义体: { MultilinearMap.pi fun a => (f a).toMultilinearMap with
    map_eq_zero_of_eq' := fun _ _ _ h hne => funext fun a => (f a).map_eq_zero_of_eq _ h hne }

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.pi, map_eq_zero_of_eq, toMultilinearMap
-/
def pi {ι' : Type*} {N : ι' -> Type*} [forall i, AddCommMonoid (N i)] [forall i, Module R (N i)]
    (f : forall i, M [⋀^ι]->ₗ[R] N i) : M [⋀^ι]->ₗ[R] (forall i, N i) :=
  { MultilinearMap.pi fun a => (f a).toMultilinearMap with
    map_eq_zero_of_eq' := fun _ _ _ h hne => funext fun a => (f a).map_eq_zero_of_eq _ h hne }

@[simp]
/--
theorem `coe_pi` / 定理 `coe_pi`

English:
theorem coe_pi
  statement: {ι' : Type*} {N : ι' -> Type*} [forall i, AddCommMonoid (N i)] [forall i, Module R (N i)]
  proof: rfl

中文:
定理 coe_pi
  结论: {ι' : 类型} {N : ι' -> 类型} [对任意 i, 加法交换幺半群 (N i)] [对任意 i, 模 R (N i)]
  证明: rfl
-/
theorem coe_pi {ι' : Type*} {N : ι' -> Type*} [forall i, AddCommMonoid (N i)] [forall i, Module R (N i)]
    (f : forall i, M [⋀^ι]->ₗ[R] N i) :
    (pi f : MultilinearMap R (fun _ : ι => M) (forall i, N i)) = MultilinearMap.pi fun a => f a :=
  rfl

/-- Given an alternating `R`-multilinear map `f` taking values in `R`, `f.smul_right z` is the map
sending `m` to `f m • z`. -/
@[simps!]
/--
Definition of `smulRight` / `smulRight` 的定义

English:
definition smulRight
  signature: {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
  body: { f.toMultilinearMap.smulRight z with
    map_eq_zero_of_eq' := fun v i j h hne => by simp [f.map_eq_zero_of_eq v h hne] }

@[simp]

中文:
定义 smulRight
  签名: {R M₁ M₂ ι : 类型} [交换半环 R] [加法交换幺半群 M₁] [加法交换幺半群 M₂]
  定义体: { f.toMultilinearMap.smulRight z with
    map_eq_zero_of_eq' := fun v i j h hne => by simp [f.map_eq_zero_of_eq v h hne] }

@[simp]

Depends on / 依赖: f.map_eq_zero_of_eq, f.toMultilinearMap.smulRight, map_eq_zero_of_eq, smulRight, toMultilinearMap
-/
def smulRight {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] (f : M₁ [⋀^ι]->ₗ[R] R) (z : M₂) : M₁ [⋀^ι]->ₗ[R] M₂ :=
  { f.toMultilinearMap.smulRight z with
    map_eq_zero_of_eq' := fun v i j h hne => by simp [f.map_eq_zero_of_eq v h hne] }

@[simp]
/--
theorem `coe_smulRight` / 定理 `coe_smulRight`

English:
theorem coe_smulRight
  statement: {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
  proof: rfl

中文:
定理 coe_smulRight
  结论: {R M₁ M₂ ι : 类型} [交换半环 R] [加法交换幺半群 M₁] [加法交换幺半群 M₂]
  证明: rfl
-/
theorem coe_smulRight {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] (f : M₁ [⋀^ι]->ₗ[R] R) (z : M₂) :
    (f.smulRight z : MultilinearMap R (fun _ : ι => M₁) M₂) = MultilinearMap.smulRight f z :=
  rfl

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add (M [⋀^ι]->ₗ[R] N) where
  body: { (a + b : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [a.map_eq_zero_of_eq v h hij, b.map_eq_zero_of_eq v h hij] }

@[simp]

中文:
实例 instAdd
  签名: : 加法 (M [⋀^ι]->ₗ[R] N) where
  定义体: { (a + b : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [a.map_eq_zero_of_eq v h hij, b.map_eq_zero_of_eq v h hij] }

@[simp]

Depends on / 依赖: MultilinearMap, a.map_eq_zero_of_eq, b.map_eq_zero_of_eq, map_eq_zero_of_eq
-/
instance instAdd : Add (M [⋀^ι]->ₗ[R] N) where
  add a b :=
    { (a + b : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [a.map_eq_zero_of_eq v h hij, b.map_eq_zero_of_eq v h hij] }

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  statement: (f + f') v = f v + f' v
  proof: rfl

@[norm_cast]

中文:
定理 add_apply
  结论: (f + f') v = f v + f' v
  证明: rfl

@[norm_cast]
-/
theorem add_apply : (f + f') v = f v + f' v :=
  rfl

@[norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  statement: (↑(f + f') : MultilinearMap R (fun _ : ι => M) N) = f + f'
  proof: rfl

中文:
定理 coe_add
  结论: (↑(f + f') : 多重线性映射 R (fun _ : ι => M) N) = f + f'
  证明: rfl
-/
theorem coe_add : (↑(f + f') : MultilinearMap R (fun _ : ι => M) N) = f + f' :=
  rfl

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (M [⋀^ι]->ₗ[R] N)
  body: ⟨{ (0 : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun _ _ _ _ _ => by simp }⟩

@[simp]

中文:
实例 instZero
  签名: : 零 (M [⋀^ι]->ₗ[R] N)
  定义体: ⟨{ (0 : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun _ _ _ _ _ => by simp }⟩

@[simp]

Depends on / 依赖: MultilinearMap, map_eq_zero_of_eq
-/
instance instZero : Zero (M [⋀^ι]->ₗ[R] N) :=
  ⟨{ (0 : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun _ _ _ _ _ => by simp }⟩

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  statement: (0 : M [⋀^ι]->ₗ[R] N) v = 0
  proof: rfl

@[norm_cast]

中文:
定理 zero_apply
  结论: (0 : M [⋀^ι]->ₗ[R] N) v = 0
  证明: rfl

@[norm_cast]
-/
theorem zero_apply : (0 : M [⋀^ι]->ₗ[R] N) v = 0 :=
  rfl

@[norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : M [⋀^ι]->ₗ[R] N) : MultilinearMap R (fun _ : ι => M) N) = 0
  proof: rfl

@[simp]

中文:
定理 coe_zero
  结论: ((0 : M [⋀^ι]->ₗ[R] N) : 多重线性映射 R (fun _ : ι => M) N) = 0
  证明: rfl

@[simp]
-/
theorem coe_zero : ((0 : M [⋀^ι]->ₗ[R] N) : MultilinearMap R (fun _ : ι => M) N) = 0 :=
  rfl

@[simp]
/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  proof: rfl

中文:
定理 mk_zero
  证明: rfl
-/
theorem mk_zero :
    mk (0 : MultilinearMap R (fun _ : ι => M) N) (0 : M [⋀^ι]->ₗ[R] N).2 = 0 :=
  rfl

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (M [⋀^ι]->ₗ[R] N)
  body: ⟨0⟩

中文:
实例 instInhabited
  签名: : 可居 (M [⋀^ι]->ₗ[R] N)
  定义体: ⟨0⟩
-/
instance instInhabited : Inhabited (M [⋀^ι]->ₗ[R] N) :=
  ⟨0⟩

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: : AddCommMonoid (M [⋀^ι]->ₗ[R] N)
  body: fast_instance%
  coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => coeFn_smul _ _

中文:
实例 instAddCommMonoid
  签名: : 加法交换幺半群 (M [⋀^ι]->ₗ[R] N)
  定义体: fast_instance%
  coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => coeFn_smul _ _

Depends on / 依赖: fast_instance
-/
instance instAddCommMonoid : AddCommMonoid (M [⋀^ι]->ₗ[R] N) := fast_instance%
  coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => coeFn_smul _ _

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg (M [⋀^ι]->ₗ[R] N')
  body: ⟨fun f =>
    { -(f : MultilinearMap R (fun _ : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩

@[simp]

中文:
实例 instNeg
  签名: : 取负 (M [⋀^ι]->ₗ[R] N')
  定义体: ⟨fun f =>
    { -(f : MultilinearMap R (fun _ : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩

@[simp]

Depends on / 依赖: MultilinearMap, f.map_eq_zero_of_eq, map_eq_zero_of_eq
-/
instance instNeg : Neg (M [⋀^ι]->ₗ[R] N') :=
  ⟨fun f =>
    { -(f : MultilinearMap R (fun _ : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩

@[simp]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: (m : ι -> M)
  statement: (-g) m = -g m
  proof: rfl

@[norm_cast]

中文:
定理 neg_apply
  条件: (m : ι -> M)
  结论: (-g) m = -g m
  证明: rfl

@[norm_cast]
-/
theorem neg_apply (m : ι -> M) : (-g) m = -g m :=
  rfl

@[norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  statement: ((-g : M [⋀^ι]->ₗ[R] N') : MultilinearMap R (fun _ : ι => M) N') = -g
  proof: rfl

中文:
定理 coe_neg
  结论: ((-g : M [⋀^ι]->ₗ[R] N') : 多重线性映射 R (fun _ : ι => M) N') = -g
  证明: rfl
-/
theorem coe_neg : ((-g : M [⋀^ι]->ₗ[R] N') : MultilinearMap R (fun _ : ι => M) N') = -g :=
  rfl

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub (M [⋀^ι]->ₗ[R] N')
  body: ⟨fun f g =>
    { (f - g : MultilinearMap R (fun _ : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [f.map_eq_zero_of_eq v h hij, g.map_eq_zero_of_eq v h hij] }⟩

@[simp]

中文:
实例 instSub
  签名: : 减法 (M [⋀^ι]->ₗ[R] N')
  定义体: ⟨fun f g =>
    { (f - g : MultilinearMap R (fun _ : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [f.map_eq_zero_of_eq v h hij, g.map_eq_zero_of_eq v h hij] }⟩

@[simp]

Depends on / 依赖: MultilinearMap, f.map_eq_zero_of_eq, g.map_eq_zero_of_eq, map_eq_zero_of_eq
-/
instance instSub : Sub (M [⋀^ι]->ₗ[R] N') :=
  ⟨fun f g =>
    { (f - g : MultilinearMap R (fun _ : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [f.map_eq_zero_of_eq v h hij, g.map_eq_zero_of_eq v h hij] }⟩

@[simp]
/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: (m : ι -> M)
  statement: (g - g₂) m = g m - g₂ m
  proof: rfl

@[norm_cast]

中文:
定理 sub_apply
  条件: (m : ι -> M)
  结论: (g - g₂) m = g m - g₂ m
  证明: rfl

@[norm_cast]
-/
theorem sub_apply (m : ι -> M) : (g - g₂) m = g m - g₂ m :=
  rfl

@[norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  statement: (↑(g - g₂) : MultilinearMap R (fun _ : ι => M) N') = g - g₂
  proof: rfl

中文:
定理 coe_sub
  结论: (↑(g - g₂) : 多重线性映射 R (fun _ : ι => M) N') = g - g₂
  证明: rfl
-/
theorem coe_sub : (↑(g - g₂) : MultilinearMap R (fun _ : ι => M) N') = g - g₂ :=
  rfl

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: : AddCommGroup (M [⋀^ι]->ₗ[R] N')
  body: fast_instance%
  coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => coeFn_smul _ _) fun _ _ => coeFn_smul _ _

中文:
实例 instAddCommGroup
  签名: : 加法交换群 (M [⋀^ι]->ₗ[R] N')
  定义体: fast_instance%
  coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => coeFn_smul _ _) fun _ _ => coeFn_smul _ _

Depends on / 依赖: fast_instance
-/
instance instAddCommGroup : AddCommGroup (M [⋀^ι]->ₗ[R] N') := fast_instance%
  coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => coeFn_smul _ _) fun _ _ => coeFn_smul _ _

section DistribMulAction

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: : DistribMulAction S (M [⋀^ι]->ₗ[R] N) where
  body: ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
  smul_zero _ := ext fun _ => smul_zero _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

中文:
实例 instDistribMulAction
  签名: : 分配乘法作用 S (M [⋀^ι]->ₗ[R] N) where
  定义体: ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
  smul_zero _ := ext fun _ => smul_zero _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

Depends on / 依赖: one_smul
-/
instance instDistribMulAction : DistribMulAction S (M [⋀^ι]->ₗ[R] N) where
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
  smul_zero _ := ext fun _ => smul_zero _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

end DistribMulAction

section Module

variable {S : Type*} [Semiring S] [Module S N] [SMulCommClass R S N]

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: : Module S (M [⋀^ι]->ₗ[R] N) where
  body: ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

中文:
实例 instModule
  签名: : 模 S (M [⋀^ι]->ₗ[R] N) where
  定义体: ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

Depends on / 依赖: add_smul
-/
instance instModule : Module S (M [⋀^ι]->ₗ[R] N) where
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

/--
Instance `instIsTorsionFree` / 实例 `instIsTorsionFree`

English:
instance instIsTorsionFree
  signature: [IsTorsionFree S N]
  body: coe_injective.moduleIsTorsionFree _ coeFn_smul

中文:
实例 instIsTorsionFree
  签名: [是无挠 S N]
  定义体: coe_injective.moduleIsTorsionFree _ coeFn_smul

Depends on / 依赖: coeFn_smul, coe_injective, coe_injective.moduleIsTorsionFree, moduleIsTorsionFree
-/
instance instIsTorsionFree [IsTorsionFree S N] : IsTorsionFree S (M [⋀^ι]->ₗ[R] N) :=
  coe_injective.moduleIsTorsionFree _ coeFn_smul

/-- Embedding of alternating maps into multilinear maps as a linear map. -/
@[simps]
/--
Definition of `toMultilinearMapLM` / `toMultilinearMapLM` 的定义

English:
definition toMultilinearMapLM
  signature: : (M [⋀^ι]->ₗ[R] N) ->ₗ[S] MultilinearMap R (fun _ : ι => M) N where
  body: toMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 toMultilinearMapLM
  签名: : (M [⋀^ι]->ₗ[R] N) ->ₗ[S] 多重线性映射 R (fun _ : ι => M) N where
  定义体: toMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: toMultilinearMap
-/
def toMultilinearMapLM : (M [⋀^ι]->ₗ[R] N) ->ₗ[S] MultilinearMap R (fun _ : ι => M) N where
  toFun := toMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Module

section

variable (R M N)

/-- The natural equivalence between linear maps from `M` to `N`
and `1`-multilinear alternating maps from `M` to `N`. -/
@[simps!]
/--
Definition of `ofSubsingleton` / `ofSubsingleton` 的定义

English:
definition ofSubsingleton
  signature: [Subsingleton ι] (i : ι)
  body: ⟨MultilinearMap.ofSubsingleton R M N i f, fun _ _ _ _ => absurd (Subsingleton.elim _ _)⟩
  invFun f := (MultilinearMap.ofSubsingleton R M N i).symm f
right_inv _ := coe_multilinearMap_injective
    (MultilinearMap.ofSubsingleton R M N i).apply_symm_apply _

中文:
定义 ofSubsingleton
  签名: [子单例 ι] (i : ι)
  定义体: ⟨MultilinearMap.ofSubsingleton R M N i f, fun _ _ _ _ => absurd (Subsingleton.elim _ _)⟩
  invFun f := (MultilinearMap.ofSubsingleton R M N i).symm f
right_inv _ := coe_multilinearMap_injective
    (MultilinearMap.ofSubsingleton R M N i).apply_symm_apply _

Depends on / 依赖: MultilinearMap, MultilinearMap.ofSubsingleton, Subsingleton, Subsingleton.elim, absurd, ofSubsingleton
-/
def ofSubsingleton [Subsingleton ι] (i : ι) : (M ->ₗ[R] N) ≃ (M [⋀^ι]->ₗ[R] N) where
  toFun f := ⟨MultilinearMap.ofSubsingleton R M N i f, fun _ _ _ _ => absurd (Subsingleton.elim _ _)⟩
  invFun f := (MultilinearMap.ofSubsingleton R M N i).symm f
right_inv _ := coe_multilinearMap_injective
    (MultilinearMap.ofSubsingleton R M N i).apply_symm_apply _

variable (ι) {N}

/-- The constant map is alternating when `ι` is empty. -/
@[simps -fullyApplied]
/--
Definition of `constOfIsEmpty` / `constOfIsEmpty` 的定义

English:
definition constOfIsEmpty
  signature: [IsEmpty ι] (m : N)
  body: { MultilinearMap.constOfIsEmpty R _ m with
    toFun := Function.const _ m
    map_eq_zero_of_eq' := fun _ => isEmptyElim }

中文:
定义 constOfIsEmpty
  签名: [是空 ι] (m : N)
  定义体: { MultilinearMap.constOfIsEmpty R _ m with
    toFun := Function.const _ m
    map_eq_zero_of_eq' := fun _ => isEmptyElim }

Depends on / 依赖: Function, Function.const, MultilinearMap, MultilinearMap.constOfIsEmpty, constOfIsEmpty, isEmptyElim, map_eq_zero_of_eq
-/
def constOfIsEmpty [IsEmpty ι] (m : N) : M [⋀^ι]->ₗ[R] N :=
  { MultilinearMap.constOfIsEmpty R _ m with
    toFun := Function.const _ m
    map_eq_zero_of_eq' := fun _ => isEmptyElim }

end

/-- Restrict the codomain of an alternating map to a submodule. -/
@[simps]
/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : M [⋀^ι]->ₗ[R] N) (p : Submodule R N) (h : forall v, f v in p)
  body: { f.toMultilinearMap.codRestrict p h with
    toFun := fun v => ⟨f v, h v⟩
map_eq_zero_of_eq' := fun _ _ _ hv hij => Subtype.ext map_eq_zero_of_eq _ _ hv hij }

中文:
定义 codRestrict
  签名: (f : M [⋀^ι]->ₗ[R] N) (p : 子模 R N) (h : 对任意 v, f v in p)
  定义体: { f.toMultilinearMap.codRestrict p h with
    toFun := fun v => ⟨f v, h v⟩
map_eq_zero_of_eq' := fun _ _ _ hv hij => Subtype.ext map_eq_zero_of_eq _ _ hv hij }

Depends on / 依赖: Subtype, Subtype.ext, codRestrict, f.toMultilinearMap.codRestrict, map_eq_zero_of_eq, toMultilinearMap
-/
def codRestrict (f : M [⋀^ι]->ₗ[R] N) (p : Submodule R N) (h : forall v, f v in p) :
    M [⋀^ι]->ₗ[R] p :=
  { f.toMultilinearMap.codRestrict p h with
    toFun := fun v => ⟨f v, h v⟩
map_eq_zero_of_eq' := fun _ _ _ hv hij => Subtype.ext map_eq_zero_of_eq _ _ hv hij }

end AlternatingMap

/-!
### Composition with linear maps
-/


namespace LinearMap

variable {S : Type*} {N₂ : Type*} [AddCommMonoid N₂] [Module R N₂]

/--
Definition of `compAlternatingMap` / `compAlternatingMap` 的定义

English:
definition compAlternatingMap
  signature: (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N)
  body: g.compMultilinearMap (f : MultilinearMap R (fun _ : ι => M) N)
  map_eq_zero_of_eq' v i j h hij := by simp [f.map_eq_zero_of_eq v h hij]

@[simp]

中文:
定义 compAlternatingMap
  签名: (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N)
  定义体: g.compMultilinearMap (f : MultilinearMap R (fun _ : ι => M) N)
  map_eq_zero_of_eq' v i j h hij := by simp [f.map_eq_zero_of_eq v h hij]

@[simp]

Depends on / 依赖: MultilinearMap, compMultilinearMap, g.compMultilinearMap
-/
def compAlternatingMap (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N) : M [⋀^ι]->ₗ[R] N₂ where
  __ := g.compMultilinearMap (f : MultilinearMap R (fun _ : ι => M) N)
  map_eq_zero_of_eq' v i j h hij := by simp [f.map_eq_zero_of_eq v h hij]

@[simp]
/--
theorem `coe_compAlternatingMap` / 定理 `coe_compAlternatingMap`

English:
theorem coe_compAlternatingMap
  given: (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N)
  proof: rfl

@[simp]

中文:
定理 coe_compAlternatingMap
  条件: (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N)
  证明: rfl

@[simp]
-/
theorem coe_compAlternatingMap (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N) :
    ⇑(g.compAlternatingMap f) = g ∘ f :=
  rfl

@[simp]
/--
theorem `compAlternatingMap_apply` / 定理 `compAlternatingMap_apply`

English:
theorem compAlternatingMap_apply
  given: (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N) (m : ι -> M)
  proof: rfl

@[simp]

中文:
定理 compAlternatingMap_apply
  条件: (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N) (m : ι -> M)
  证明: rfl

@[simp]
-/
theorem compAlternatingMap_apply (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N) (m : ι -> M) :
    g.compAlternatingMap f m = g (f m) :=
  rfl

@[simp]
/--
theorem `compAlternatingMap_zero` / 定理 `compAlternatingMap_zero`

English:
theorem compAlternatingMap_zero
  given: (g : N ->ₗ[R] N₂)
  proof: AlternatingMap.ext fun _ => map_zero g

@[simp]

中文:
定理 compAlternatingMap_zero
  条件: (g : N ->ₗ[R] N₂)
  证明: AlternatingMap.ext fun _ => map_zero g

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.ext, map_zero
-/
theorem compAlternatingMap_zero (g : N ->ₗ[R] N₂) :
    g.compAlternatingMap (0 : M [⋀^ι]->ₗ[R] N) = 0 :=
  AlternatingMap.ext fun _ => map_zero g

@[simp]
/--
theorem `zero_compAlternatingMap` / 定理 `zero_compAlternatingMap`

English:
theorem zero_compAlternatingMap
  given: (f : M [⋀^ι]->ₗ[R] N)
  proof: rfl

@[simp]

中文:
定理 zero_compAlternatingMap
  条件: (f : M [⋀^ι]->ₗ[R] N)
  证明: rfl

@[simp]
-/
theorem zero_compAlternatingMap (f : M [⋀^ι]->ₗ[R] N) :
    (0 : N ->ₗ[R] N₂).compAlternatingMap f = 0 := rfl

@[simp]
/--
theorem `compAlternatingMap_add` / 定理 `compAlternatingMap_add`

English:
theorem compAlternatingMap_add
  given: (g : N ->ₗ[R] N₂) (f₁ f₂ : M [⋀^ι]->ₗ[R] N)
  proof: AlternatingMap.ext fun _ => map_add g _ _

@[simp]

中文:
定理 compAlternatingMap_add
  条件: (g : N ->ₗ[R] N₂) (f₁ f₂ : M [⋀^ι]->ₗ[R] N)
  证明: AlternatingMap.ext fun _ => map_add g _ _

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.ext, map_add
-/
theorem compAlternatingMap_add (g : N ->ₗ[R] N₂) (f₁ f₂ : M [⋀^ι]->ₗ[R] N) :
    g.compAlternatingMap (f₁ + f₂) = g.compAlternatingMap f₁ + g.compAlternatingMap f₂ :=
  AlternatingMap.ext fun _ => map_add g _ _

@[simp]
/--
theorem `add_compAlternatingMap` / 定理 `add_compAlternatingMap`

English:
theorem add_compAlternatingMap
  given: (g₁ g₂ : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N)
  proof: rfl

@[simp]

中文:
定理 add_compAlternatingMap
  条件: (g₁ g₂ : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N)
  证明: rfl

@[simp]
-/
theorem add_compAlternatingMap (g₁ g₂ : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N) :
    (g₁ + g₂).compAlternatingMap f = g₁.compAlternatingMap f + g₂.compAlternatingMap f := rfl

@[simp]
/--
theorem `compAlternatingMap_smul` / 定理 `compAlternatingMap_smul`

English:
theorem compAlternatingMap_smul
  statement: [Monoid S] [DistribMulAction S N] [DistribMulAction S N₂]
  proof: AlternatingMap.ext fun _ => g.map_smul_of_tower _ _

@[simp]

中文:
定理 compAlternatingMap_smul
  结论: [幺半群 S] [分配乘法作用 S N] [分配乘法作用 S N₂]
  证明: AlternatingMap.ext fun _ => g.map_smul_of_tower _ _

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.ext, g.map_smul_of_tower, map_smul_of_tower
-/
theorem compAlternatingMap_smul [Monoid S] [DistribMulAction S N] [DistribMulAction S N₂]
    [SMulCommClass R S N] [SMulCommClass R S N₂] [CompatibleSMul N N₂ S R]
    (g : N ->ₗ[R] N₂) (s : S) (f : M [⋀^ι]->ₗ[R] N) :
    g.compAlternatingMap (s • f) = s • g.compAlternatingMap f :=
  AlternatingMap.ext fun _ => g.map_smul_of_tower _ _

@[simp]
/--
theorem `smul_compAlternatingMap` / 定理 `smul_compAlternatingMap`

English:
theorem smul_compAlternatingMap
  statement: [Monoid S] [DistribMulAction S N₂] [SMulCommClass R S N₂]
  proof: rfl

中文:
定理 smul_compAlternatingMap
  结论: [幺半群 S] [分配乘法作用 S N₂] [标量交换类 R S N₂]
  证明: rfl
-/
theorem smul_compAlternatingMap [Monoid S] [DistribMulAction S N₂] [SMulCommClass R S N₂]
    (g : N ->ₗ[R] N₂) (s : S) (f : M [⋀^ι]->ₗ[R] N) :
    (s • g).compAlternatingMap f = s • g.compAlternatingMap f := rfl

variable (S) in
/-- `LinearMap.compAlternatingMap` as an `S`-linear map. -/
@[simps]
/--
Definition of `compAlternatingMapₗ` / `compAlternatingMapₗ` 的定义

English:
definition compAlternatingMapₗ
  signature: [Semiring S] [Module S N] [Module S N₂]
  body: g.compAlternatingMap
  map_add' := g.compAlternatingMap_add
  map_smul' := g.compAlternatingMap_smul

中文:
定义 compAlternatingMapₗ
  签名: [半环 S] [模 S N] [模 S N₂]
  定义体: g.compAlternatingMap
  map_add' := g.compAlternatingMap_add
  map_smul' := g.compAlternatingMap_smul

Depends on / 依赖: compAlternatingMap, g.compAlternatingMap
-/
def compAlternatingMapₗ [Semiring S] [Module S N] [Module S N₂]
    [SMulCommClass R S N] [SMulCommClass R S N₂] [LinearMap.CompatibleSMul N N₂ S R]
    (g : N ->ₗ[R] N₂) :
    (M [⋀^ι]->ₗ[R] N) ->ₗ[S] (M [⋀^ι]->ₗ[R] N₂) where
  toFun := g.compAlternatingMap
  map_add' := g.compAlternatingMap_add
  map_smul' := g.compAlternatingMap_smul

/--
theorem `_root_.AlternatingMap.smulRight_eq_comp` / 定理 `_root_.AlternatingMap.smulRight_eq_comp`

English:
theorem _root_.AlternatingMap.smulRight_eq_comp
  proof: rfl

@[deprecated (since := "2026-05-14")]
alias smulRight_eq_comp := AlternatingMap.smulRight_eq_comp

@[simp]

中文:
定理 _root_.交错映射.smulRight_eq_comp
  证明: rfl

@[deprecated (since := "2026-05-14")]
alias smulRight_eq_comp := AlternatingMap.smulRight_eq_comp

@[simp]
-/
theorem _root_.AlternatingMap.smulRight_eq_comp
    {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [Module R M₁] [Module R M₂] (f : M₁ [⋀^ι]->ₗ[R] R) (z : M₂) :
    f.smulRight z = (LinearMap.id.smulRight z).compAlternatingMap f :=
  rfl

@[deprecated (since := "2026-05-14")]
alias smulRight_eq_comp := AlternatingMap.smulRight_eq_comp

@[simp]
/--
theorem `subtype_compAlternatingMap_codRestrict` / 定理 `subtype_compAlternatingMap_codRestrict`

English:
theorem subtype_compAlternatingMap_codRestrict
  statement: (f : M [⋀^ι]->ₗ[R] N) (p : Submodule R N)
  proof: AlternatingMap.ext fun _ => rfl

@[simp]

中文:
定理 subtype_compAlternatingMap_codRestrict
  结论: (f : M [⋀^ι]->ₗ[R] N) (p : 子模 R N)
  证明: AlternatingMap.ext fun _ => rfl

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.ext
-/
theorem subtype_compAlternatingMap_codRestrict (f : M [⋀^ι]->ₗ[R] N) (p : Submodule R N)
    (h) : p.subtype.compAlternatingMap (f.codRestrict p h) = f :=
  AlternatingMap.ext fun _ => rfl

@[simp]
/--
theorem `compAlternatingMap_codRestrict` / 定理 `compAlternatingMap_codRestrict`

English:
theorem compAlternatingMap_codRestrict
  statement: (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N)
  proof: AlternatingMap.ext fun _ => rfl

中文:
定理 compAlternatingMap_codRestrict
  结论: (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N)
  证明: AlternatingMap.ext fun _ => rfl

Depends on / 依赖: AlternatingMap, AlternatingMap.ext
-/
theorem compAlternatingMap_codRestrict (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N)
    (p : Submodule R N₂) (h) :
    (g.codRestrict p h).compAlternatingMap f =
      (g.compAlternatingMap f).codRestrict p fun v => h (f v) :=
  AlternatingMap.ext fun _ => rfl

end LinearMap

namespace AlternatingMap

variable {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂]
variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃]

/--
Definition of `compLinearMap` / `compLinearMap` 的定义

English:
definition compLinearMap
  signature: (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M)
  body: { (f : MultilinearMap R (fun _ : ι => M) N).compLinearMap fun _ => g with
    map_eq_zero_of_eq' := fun _ _ _ h hij => f.map_eq_zero_of_eq _ (LinearMap.congr_arg h) hij }

中文:
定义 compLinearMap
  签名: (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M)
  定义体: { (f : MultilinearMap R (fun _ : ι => M) N).compLinearMap fun _ => g with
    map_eq_zero_of_eq' := fun _ _ _ h hij => f.map_eq_zero_of_eq _ (LinearMap.congr_arg h) hij }

Depends on / 依赖: LinearMap, LinearMap.congr_arg, MultilinearMap, compLinearMap, congr_arg, f.map_eq_zero_of_eq, map_eq_zero_of_eq
-/
def compLinearMap (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M) : M₂ [⋀^ι]->ₗ[R] N :=
  { (f : MultilinearMap R (fun _ : ι => M) N).compLinearMap fun _ => g with
    map_eq_zero_of_eq' := fun _ _ _ h hij => f.map_eq_zero_of_eq _ (LinearMap.congr_arg h) hij }

/--
theorem `coe_compLinearMap` / 定理 `coe_compLinearMap`

English:
theorem coe_compLinearMap
  given: (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M)
  proof: rfl

@[simp]

中文:
定理 coe_compLinearMap
  条件: (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M)
  证明: rfl

@[simp]
-/
theorem coe_compLinearMap (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M) :
    ⇑(f.compLinearMap g) = f ∘ (g ∘ ·) :=
  rfl

@[simp]
/--
theorem `compLinearMap_apply` / 定理 `compLinearMap_apply`

English:
theorem compLinearMap_apply
  given: (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M) (v : ι -> M₂)
  proof: rfl

中文:
定理 compLinearMap_apply
  条件: (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M) (v : ι -> M₂)
  证明: rfl
-/
theorem compLinearMap_apply (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M) (v : ι -> M₂) :
    f.compLinearMap g v = f fun i => g (v i) :=
  rfl

/--
theorem `compLinearMap_assoc` / 定理 `compLinearMap_assoc`

English:
theorem compLinearMap_assoc
  given: (f : M [⋀^ι]->ₗ[R] N) (g₁ : M₂ ->ₗ[R] M) (g₂ : M₃ ->ₗ[R] M₂)
  proof: rfl

@[simp]

中文:
定理 compLinearMap_assoc
  条件: (f : M [⋀^ι]->ₗ[R] N) (g₁ : M₂ ->ₗ[R] M) (g₂ : M₃ ->ₗ[R] M₂)
  证明: rfl

@[simp]
-/
theorem compLinearMap_assoc (f : M [⋀^ι]->ₗ[R] N) (g₁ : M₂ ->ₗ[R] M) (g₂ : M₃ ->ₗ[R] M₂) :
    (f.compLinearMap g₁).compLinearMap g₂ = f.compLinearMap (g₁ ∘ₗ g₂) :=
  rfl

@[simp]
/--
theorem `zero_compLinearMap` / 定理 `zero_compLinearMap`

English:
theorem zero_compLinearMap
  given: (g : M₂ ->ₗ[R] M)
  statement: (0 : M [⋀^ι]->ₗ[R] N).compLinearMap g = 0
  proof: by
  ext
  simp only [compLinearMap_apply, zero_apply]

@[simp]

中文:
定理 zero_compLinearMap
  条件: (g : M₂ ->ₗ[R] M)
  结论: (0 : M [⋀^ι]->ₗ[R] N).compLinearMap g = 0
  证明: by
  ext
  simp only [compLinearMap_apply, zero_apply]

@[simp]

Depends on / 依赖: compLinearMap_apply, zero_apply
-/
theorem zero_compLinearMap (g : M₂ ->ₗ[R] M) : (0 : M [⋀^ι]->ₗ[R] N).compLinearMap g = 0 := by
  ext
  simp only [compLinearMap_apply, zero_apply]

@[simp]
/--
theorem `add_compLinearMap` / 定理 `add_compLinearMap`

English:
theorem add_compLinearMap
  given: (f₁ f₂ : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M)
  proof: by
  ext
  simp only [compLinearMap_apply, add_apply]

@[simp]

中文:
定理 add_compLinearMap
  条件: (f₁ f₂ : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M)
  证明: by
  ext
  simp only [compLinearMap_apply, add_apply]

@[simp]

Depends on / 依赖: add_apply, compLinearMap_apply
-/
theorem add_compLinearMap (f₁ f₂ : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M) :
    (f₁ + f₂).compLinearMap g = f₁.compLinearMap g + f₂.compLinearMap g := by
  ext
  simp only [compLinearMap_apply, add_apply]

@[simp]
/--
theorem `compLinearMap_zero` / 定理 `compLinearMap_zero`

English:
theorem compLinearMap_zero
  given: [Nonempty ι] (f : M [⋀^ι]->ₗ[R] N)
  proof: by
  ext
  simp_rw [compLinearMap_apply, LinearMap.zero_apply, ← Pi.zero_def, map_zero, zero_apply]

中文:
定理 compLinearMap_zero
  条件: [非空 ι] (f : M [⋀^ι]->ₗ[R] N)
  证明: by
  ext
  simp_rw [compLinearMap_apply, LinearMap.zero_apply, ← Pi.zero_def, map_zero, zero_apply]

Depends on / 依赖: LinearMap, LinearMap.zero_apply, Pi.zero_def, compLinearMap_apply, map_zero, simp_rw, zero_apply, zero_def
-/
theorem compLinearMap_zero [Nonempty ι] (f : M [⋀^ι]->ₗ[R] N) :
    f.compLinearMap (0 : M₂ ->ₗ[R] M) = 0 := by
  ext
  simp_rw [compLinearMap_apply, LinearMap.zero_apply, ← Pi.zero_def, map_zero, zero_apply]

/-- Composing an alternating map with the identity linear map in each argument. -/
@[simp]
/--
theorem `compLinearMap_id` / 定理 `compLinearMap_id`

English:
theorem compLinearMap_id
  given: (f : M [⋀^ι]->ₗ[R] N)
  statement: f.compLinearMap LinearMap.id = f
  proof: ext fun _ => rfl

中文:
定理 compLinearMap_id
  条件: (f : M [⋀^ι]->ₗ[R] N)
  结论: f.compLinearMap 线性映射.id = f
  证明: ext fun _ => rfl
-/
theorem compLinearMap_id (f : M [⋀^ι]->ₗ[R] N) : f.compLinearMap LinearMap.id = f :=
  ext fun _ => rfl

/--
theorem `compLinearMap_injective` / 定理 `compLinearMap_injective`

English:
theorem compLinearMap_injective
  given: (f : M₂ ->ₗ[R] M) (hf : Function.Surjective f)
  proof: fun g₁ g₂ h =>
  ext fun x => by
    simpa [Function.surjInv_eq hf] using AlternatingMap.ext_iff.mp h (Function.surjInv hf ∘ x)

中文:
定理 compLinearMap_injective
  条件: (f : M₂ ->ₗ[R] M) (hf : 函数.满射 f)
  证明: fun g₁ g₂ h =>
  ext fun x => by
    simpa [Function.surjInv_eq hf] using AlternatingMap.ext_iff.mp h (Function.surjInv hf ∘ x)
-/
theorem compLinearMap_injective (f : M₂ ->ₗ[R] M) (hf : Function.Surjective f) :
    Function.Injective fun g : M [⋀^ι]->ₗ[R] N => g.compLinearMap f := fun g₁ g₂ h =>
  ext fun x => by
    simpa [Function.surjInv_eq hf] using AlternatingMap.ext_iff.mp h (Function.surjInv hf ∘ x)

/--
theorem `compLinearMap_inj` / 定理 `compLinearMap_inj`

English:
theorem compLinearMap_inj
  statement: (f : M₂ ->ₗ[R] M) (hf : Function.Surjective f)
  proof: (compLinearMap_injective _ hf).eq_iff

中文:
定理 compLinearMap_inj
  结论: (f : M₂ ->ₗ[R] M) (hf : 函数.满射 f)
  证明: (compLinearMap_injective _ hf).eq_iff

Depends on / 依赖: compLinearMap_injective, eq_iff
-/
theorem compLinearMap_inj (f : M₂ ->ₗ[R] M) (hf : Function.Surjective f)
    (g₁ g₂ : M [⋀^ι]->ₗ[R] N) : g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂ :=
  (compLinearMap_injective _ hf).eq_iff

/-- If two `R`-alternating maps from `R` are equal on 1, then they are equal.

This is the alternating version of `LinearMap.ext_ring`. -/
@[ext]
/--
theorem `ext_ring` / 定理 `ext_ring`

English:
theorem ext_ring
  given: {R} [CommSemiring R] [Module R N] [Finite ι] ⦃f g
  statement: R [⋀^ι]->ₗ[R] N⦄
  proof: coe_multilinearMap_injective MultilinearMap.ext_ring h

中文:
定理 ext_ring
  条件: {R} [交换半环 R] [模 R N] [有限 ι] ⦃f g
  结论: R [⋀^ι]->ₗ[R] N⦄
  证明: coe_multilinearMap_injective MultilinearMap.ext_ring h

Depends on / 依赖: MultilinearMap, MultilinearMap.ext_ring, coe_multilinearMap_injective, ext_ring
-/
theorem ext_ring {R} [CommSemiring R] [Module R N] [Finite ι] ⦃f g : R [⋀^ι]->ₗ[R] N⦄
    (h : f (fun _ => 1) = g (fun _ => 1)) : f = g :=
coe_multilinearMap_injective MultilinearMap.ext_ring h

/--
Instance `uniqueOfCommRing` / 实例 `uniqueOfCommRing`

English:
instance uniqueOfCommRing
  signature: {R} [CommSemiring R] [Module R N] [Finite ι] [Nontrivial ι]
  body: let ⟨_, _, hij⟩ := exists_pair_ne ι; ext_ring f.map_eq_zero_of_eq _ rfl hij

中文:
实例 uniqueOfCommRing
  签名: {R} [交换半环 R] [模 R N] [有限 ι] [非平凡 ι]
  定义体: let ⟨_, _, hij⟩ := exists_pair_ne ι; ext_ring f.map_eq_zero_of_eq _ rfl hij

Depends on / 依赖: exists_pair_ne, ext_ring, f.map_eq_zero_of_eq, map_eq_zero_of_eq
-/
instance uniqueOfCommRing {R} [CommSemiring R] [Module R N] [Finite ι] [Nontrivial ι] :
    Unique (R [⋀^ι]->ₗ[R] N) where
uniq f := let ⟨_, _, hij⟩ := exists_pair_ne ι; ext_ring f.map_eq_zero_of_eq _ rfl hij

section DomLcongr

variable (ι R N)
variable (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N]

/-- Construct a linear equivalence between maps from a linear equivalence between domains.

This is `AlternatingMap.compLinearMap` as an isomorphism,
and the alternating version of `LinearEquiv.multilinearMapCongrLeft`.
It could also have been called `LinearEquiv.alternatingMapCongrLeft`. -/
@[simps apply]
/--
Definition of `domLCongr` / `domLCongr` 的定义

English:
definition domLCongr
  signature: (e : M ≃ₗ[R] M₂)
  body: f.compLinearMap e.symm
  invFun g := g.compLinearMap e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
left_inv f := AlternatingMap.ext fun _ => f.congr_arg funext fun _ => e.symm_apply_apply _
right_inv f := AlternatingMap.ext fun _ => f.congr_arg funext fun _ => e.apply_symm_apply _

@[simp]

中文:
定义 domLCongr
  签名: (e : M ≃ₗ[R] M₂)
  定义体: f.compLinearMap e.symm
  invFun g := g.compLinearMap e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
left_inv f := AlternatingMap.ext fun _ => f.congr_arg funext fun _ => e.symm_apply_apply _
right_inv f := AlternatingMap.ext fun _ => f.congr_arg funext fun _ => e.apply_symm_apply _

@[simp]

Depends on / 依赖: compLinearMap, e.symm, f.compLinearMap
-/
def domLCongr (e : M ≃ₗ[R] M₂) : M [⋀^ι]->ₗ[R] N ≃ₗ[S] (M₂ [⋀^ι]->ₗ[R] N) where
  toFun f := f.compLinearMap e.symm
  invFun g := g.compLinearMap e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
left_inv f := AlternatingMap.ext fun _ => f.congr_arg funext fun _ => e.symm_apply_apply _
right_inv f := AlternatingMap.ext fun _ => f.congr_arg funext fun _ => e.apply_symm_apply _

@[simp]
/--
theorem `domLCongr_refl` / 定理 `domLCongr_refl`

English:
theorem domLCongr_refl
  statement: domLCongr R N ι S (LinearEquiv.refl R M) = LinearEquiv.refl S _
  proof: LinearEquiv.ext fun _ => AlternatingMap.ext fun _ => rfl

@[simp]

中文:
定理 domLCongr_refl
  结论: domLCongr R N ι S (线性等价.refl R M) = 线性等价.refl S _
  证明: LinearEquiv.ext fun _ => AlternatingMap.ext fun _ => rfl

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.ext, LinearEquiv, LinearEquiv.ext
-/
theorem domLCongr_refl : domLCongr R N ι S (LinearEquiv.refl R M) = LinearEquiv.refl S _ :=
  LinearEquiv.ext fun _ => AlternatingMap.ext fun _ => rfl

@[simp]
/--
theorem `domLCongr_symm` / 定理 `domLCongr_symm`

English:
theorem domLCongr_symm
  given: (e : M ≃ₗ[R] M₂)
  statement: (domLCongr R N ι S e).symm = domLCongr R N ι S e.symm
  proof: rfl

中文:
定理 domLCongr_symm
  条件: (e : M ≃ₗ[R] M₂)
  结论: (domLCongr R N ι S e).symm = domLCongr R N ι S e.symm
  证明: rfl
-/
theorem domLCongr_symm (e : M ≃ₗ[R] M₂) : (domLCongr R N ι S e).symm = domLCongr R N ι S e.symm :=
  rfl

/--
theorem `domLCongr_trans` / 定理 `domLCongr_trans`

English:
theorem domLCongr_trans
  given: (e : M ≃ₗ[R] M₂) (f : M₂ ≃ₗ[R] M₃)
  proof: rfl

中文:
定理 domLCongr_trans
  条件: (e : M ≃ₗ[R] M₂) (f : M₂ ≃ₗ[R] M₃)
  证明: rfl
-/
theorem domLCongr_trans (e : M ≃ₗ[R] M₂) (f : M₂ ≃ₗ[R] M₃) :
    (domLCongr R N ι S e).trans (domLCongr R N ι S f) = domLCongr R N ι S (e.trans f) :=
  rfl

end DomLcongr

/-- Composing an alternating map with the same linear equiv on each argument gives the zero map
if and only if the alternating map is the zero map. -/
@[simp]
/--
theorem `compLinearEquiv_eq_zero_iff` / 定理 `compLinearEquiv_eq_zero_iff`

English:
theorem compLinearEquiv_eq_zero_iff
  given: (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ≃ₗ[R] M)
  proof: (domLCongr R N ι Nat g.symm).map_eq_zero_iff

中文:
定理 compLinearEquiv_eq_zero_iff
  条件: (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ≃ₗ[R] M)
  证明: (domLCongr R N ι Nat g.symm).map_eq_zero_iff

Depends on / 依赖: domLCongr, g.symm, map_eq_zero_iff
-/
theorem compLinearEquiv_eq_zero_iff (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ≃ₗ[R] M) :
    f.compLinearMap (g : M₂ ->ₗ[R] M) = 0 ↔ f = 0 :=
  (domLCongr R N ι Nat g.symm).map_eq_zero_iff

variable (f f' : M [⋀^ι]->ₗ[R] N)
variable (g g₂ : M [⋀^ι]->ₗ[R] N')
variable (g' : M' [⋀^ι]->ₗ[R] N')
variable (v : ι -> M) (v' : ι -> M')

open Function

/-!
### Other lemmas from `MultilinearMap`
-/


section

/--
theorem `map_update_sum` / 定理 `map_update_sum`

English:
theorem map_update_sum
  given: {α : Type*} [DecidableEq ι] (t : Finset α) (i : ι) (g : α -> M) (m : ι -> M)
  proof: f.toMultilinearMap.map_update_sum t i g m

中文:
定理 map_update_sum
  条件: {α : 类型} [DecidableEq ι] (t : 有限集 α) (i : ι) (g : α -> M) (m : ι -> M)
  证明: f.toMultilinearMap.map_update_sum t i g m

Depends on / 依赖: f.toMultilinearMap.map_update_sum, map_update_sum, toMultilinearMap
-/
theorem map_update_sum {α : Type*} [DecidableEq ι] (t : Finset α) (i : ι) (g : α -> M) (m : ι -> M) :
    f (update m i (∑ a in t, g a)) = ∑ a in t, f (update m i (g a)) :=
  f.toMultilinearMap.map_update_sum t i g m

/--
theorem `map_add_univ` / 定理 `map_add_univ`

English:
theorem map_add_univ
  given: [DecidableEq ι] [Fintype ι] (m m' : ι -> M)
  proof: f.toMultilinearMap.map_add_univ m m'

中文:
定理 map_add_univ
  条件: [DecidableEq ι] [有限类型 ι] (m m' : ι -> M)
  证明: f.toMultilinearMap.map_add_univ m m'

Depends on / 依赖: f.toMultilinearMap.map_add_univ, map_add_univ, toMultilinearMap
-/
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ι -> M) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') :=
  f.toMultilinearMap.map_add_univ m m'

/--
theorem `map_smul_univ` / 定理 `map_smul_univ`

English:
theorem map_smul_univ
  statement: {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M]
  proof: f.toMultilinearMap.map_smul_univ c m

中文:
定理 map_smul_univ
  结论: {R : 类型} [交换半环 R] {M : 类型} [加法交换幺半群 M]
  证明: f.toMultilinearMap.map_smul_univ c m

Depends on / 依赖: f.toMultilinearMap.map_smul_univ, map_smul_univ, toMultilinearMap
-/
theorem map_smul_univ {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] {N : Type*} [AddCommMonoid N] [Module R N] [Fintype ι]
    (f : M [⋀^ι]->ₗ[R] N) (c : ι -> R) (m : ι -> M) :
    (f fun i => c i • m i) = (∏ i, c i) • f m :=
  f.toMultilinearMap.map_smul_univ c m

end



/--
theorem `map_update_self` / 定理 `map_update_self`

English:
theorem map_update_self
  given: [DecidableEq ι] {i j : ι} (hij : i != j)
  proof: f.map_eq_zero_of_eq _ (by rw [Function.update_self, Function.update_of_ne hij.symm]) hij

中文:
定理 map_update_self
  条件: [DecidableEq ι] {i j : ι} (hij : i != j)
  证明: f.map_eq_zero_of_eq _ (by rw [Function.update_self, Function.update_of_ne hij.symm]) hij

Depends on / 依赖: Function, Function.update_of_ne, Function.update_self, f.map_eq_zero_of_eq, hij.symm, map_eq_zero_of_eq, update_of_ne, update_self
-/
theorem map_update_self [DecidableEq ι] {i j : ι} (hij : i != j) :
    f (Function.update v i (v j)) = 0 :=
  f.map_eq_zero_of_eq _ (by rw [Function.update_self, Function.update_of_ne hij.symm]) hij

/--
theorem `map_update_update` / 定理 `map_update_update`

English:
theorem map_update_update
  given: [DecidableEq ι] {i j : ι} (hij : i != j) (m : M)
  proof: f.map_eq_zero_of_eq _
    (by rw [Function.update_self, Function.update_of_ne hij, Function.update_self]) hij

中文:
定理 map_update_update
  条件: [DecidableEq ι] {i j : ι} (hij : i != j) (m : M)
  证明: f.map_eq_zero_of_eq _
    (by rw [Function.update_self, Function.update_of_ne hij, Function.update_self]) hij

Depends on / 依赖: Function, Function.update_of_ne, Function.update_self, f.map_eq_zero_of_eq, map_eq_zero_of_eq, update_of_ne, update_self
-/
theorem map_update_update [DecidableEq ι] {i j : ι} (hij : i != j) (m : M) :
    f (Function.update (Function.update v i m) j m) = 0 :=
  f.map_eq_zero_of_eq _
    (by rw [Function.update_self, Function.update_of_ne hij, Function.update_self]) hij

/--
theorem `map_swap_add` / 定理 `map_swap_add`

English:
theorem map_swap_add
  given: [DecidableEq ι] {i j : ι} (hij : i != j)
  proof: by
  rw [Equiv.comp_swap_eq_update]
  convert! f.map_update_update v hij (v i + v j)
  simp [f.map_update_self _ hij, f.map_update_self _ hij.symm,
    Function.update_comm hij (v i + v j) (v _) v, Function.update_comm hij.symm (v i) (v i) v]

中文:
定理 map_swap_add
  条件: [DecidableEq ι] {i j : ι} (hij : i != j)
  证明: by
  rw [Equiv.comp_swap_eq_update]
  convert! f.map_update_update v hij (v i + v j)
  simp [f.map_update_self _ hij, f.map_update_self _ hij.symm,
    Function.update_comm hij (v i + v j) (v _) v, Function.update_comm hij.symm (v i) (v i) v]

Depends on / 依赖: Equiv.comp_swap_eq_update, Function, Function.update_comm, comp_swap_eq_update, convert, f.map_update_self, f.map_update_update, hij.symm, map_update_self, map_update_update, update_comm
-/
theorem map_swap_add [DecidableEq ι] {i j : ι} (hij : i != j) :
    f (v ∘ Equiv.swap i j) + f v = 0 := by
  rw [Equiv.comp_swap_eq_update]
  convert! f.map_update_update v hij (v i + v j)
  simp [f.map_update_self _ hij, f.map_update_self _ hij.symm,
    Function.update_comm hij (v i + v j) (v _) v, Function.update_comm hij.symm (v i) (v i) v]

/--
theorem `map_add_swap` / 定理 `map_add_swap`

English:
theorem map_add_swap
  given: [DecidableEq ι] {i j : ι} (hij : i != j)
  proof: by
  rw [add_comm]
  exact f.map_swap_add v hij

中文:
定理 map_add_swap
  条件: [DecidableEq ι] {i j : ι} (hij : i != j)
  证明: by
  rw [add_comm]
  exact f.map_swap_add v hij

Depends on / 依赖: add_comm, f.map_swap_add, map_swap_add
-/
theorem map_add_swap [DecidableEq ι] {i j : ι} (hij : i != j) :
    f v + f (v ∘ Equiv.swap i j) = 0 := by
  rw [add_comm]
  exact f.map_swap_add v hij

/--
theorem `map_swap` / 定理 `map_swap`

English:
theorem map_swap
  given: [DecidableEq ι] {i j : ι} (hij : i != j)
  statement: g (v ∘ Equiv.swap i j) = -g v
  proof: eq_neg_of_add_eq_zero_left g.map_swap_add v hij

中文:
定理 map_swap
  条件: [DecidableEq ι] {i j : ι} (hij : i != j)
  结论: g (v ∘ 等价.swap i j) = -g v
  证明: eq_neg_of_add_eq_zero_left g.map_swap_add v hij

Depends on / 依赖: eq_neg_of_add_eq_zero_left, g.map_swap_add, map_swap_add
-/
theorem map_swap [DecidableEq ι] {i j : ι} (hij : i != j) : g (v ∘ Equiv.swap i j) = -g v :=
eq_neg_of_add_eq_zero_left g.map_swap_add v hij

/--
theorem `map_perm` / 定理 `map_perm`

English:
theorem map_perm
  given: [DecidableEq ι] [Fintype ι] (v : ι -> M) (σ : Equiv.Perm ι)
  proof: by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap s x y hxy hI => simp_all [← Function.comp_assoc, g.map_swap]

中文:
定理 map_perm
  条件: [DecidableEq ι] [有限类型 ι] (v : ι -> M) (σ : 等价.置换 ι)
  证明: by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap s x y hxy hI => simp_all [← Function.comp_assoc, g.map_swap]

Depends on / 依赖: Equiv.Perm.swap_induction_on, Function, Function.comp_assoc, comp_assoc, g.map_swap, map_swap, mul_swap, swap_induction_on
-/
theorem map_perm [DecidableEq ι] [Fintype ι] (v : ι -> M) (σ : Equiv.Perm ι) :
    g (v ∘ σ) = Equiv.Perm.sign σ • g v := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap s x y hxy hI => simp_all [← Function.comp_assoc, g.map_swap]

/--
theorem `map_congr_perm` / 定理 `map_congr_perm`

English:
theorem map_congr_perm
  given: [DecidableEq ι] [Fintype ι] (σ : Equiv.Perm ι)
  proof: by
  rw [g.map_perm]; rw [smul_smul]
  simp

中文:
定理 map_congr_perm
  条件: [DecidableEq ι] [有限类型 ι] (σ : 等价.置换 ι)
  证明: by
  rw [g.map_perm]; rw [smul_smul]
  simp

Depends on / 依赖: g.map_perm, map_perm, smul_smul
-/
theorem map_congr_perm [DecidableEq ι] [Fintype ι] (σ : Equiv.Perm ι) :
    g v = Equiv.Perm.sign σ • g (v ∘ σ) := by
  rw [g.map_perm]; rw [smul_smul]
  simp

section DomDomCongr

/-- Transfer the arguments to a map along an equivalence between argument indices.

This is the alternating version of `MultilinearMap.domDomCongr`. -/
@[simps]
/--
Definition of `domDomCongr` / `domDomCongr` 的定义

English:
definition domDomCongr
  signature: (σ : ι ≃ ι') (f : M [⋀^ι]->ₗ[R] N)
  body: { f.toMultilinearMap.domDomCongr σ with
    toFun := fun v => f (v ∘ σ)
    map_eq_zero_of_eq' := fun v i j hv hij =>
      f.map_eq_zero_of_eq (v ∘ σ) (i := σ.symm i) (j := σ.symm j)
        (by simpa using hv) (σ.symm.injective.ne hij) }

@[simp]

中文:
定义 domDomCongr
  签名: (σ : ι ≃ ι') (f : M [⋀^ι]->ₗ[R] N)
  定义体: { f.toMultilinearMap.domDomCongr σ with
    toFun := fun v => f (v ∘ σ)
    map_eq_zero_of_eq' := fun v i j hv hij =>
      f.map_eq_zero_of_eq (v ∘ σ) (i := σ.symm i) (j := σ.symm j)
        (by simpa using hv) (σ.symm.injective.ne hij) }

@[simp]

Depends on / 依赖: domDomCongr, f.map_eq_zero_of_eq, f.toMultilinearMap.domDomCongr, injective, map_eq_zero_of_eq, symm.injective.ne, toMultilinearMap
-/
def domDomCongr (σ : ι ≃ ι') (f : M [⋀^ι]->ₗ[R] N) : M [⋀^ι']->ₗ[R] N :=
  { f.toMultilinearMap.domDomCongr σ with
    toFun := fun v => f (v ∘ σ)
    map_eq_zero_of_eq' := fun v i j hv hij =>
      f.map_eq_zero_of_eq (v ∘ σ) (i := σ.symm i) (j := σ.symm j)
        (by simpa using hv) (σ.symm.injective.ne hij) }

@[simp]
/--
theorem `domDomCongr_refl` / 定理 `domDomCongr_refl`

English:
theorem domDomCongr_refl
  given: (f : M [⋀^ι]->ₗ[R] N)
  statement: f.domDomCongr (Equiv.refl ι) = f
  proof: rfl

中文:
定理 domDomCongr_refl
  条件: (f : M [⋀^ι]->ₗ[R] N)
  结论: f.domDomCongr (等价.refl ι) = f
  证明: rfl
-/
theorem domDomCongr_refl (f : M [⋀^ι]->ₗ[R] N) : f.domDomCongr (Equiv.refl ι) = f := rfl

/--
theorem `domDomCongr_trans` / 定理 `domDomCongr_trans`

English:
theorem domDomCongr_trans
  given: (σ₁ : ι ≃ ι') (σ₂ : ι' ≃ ι'') (f : M [⋀^ι]->ₗ[R] N)
  proof: rfl

@[simp]

中文:
定理 domDomCongr_trans
  条件: (σ₁ : ι ≃ ι') (σ₂ : ι' ≃ ι'') (f : M [⋀^ι]->ₗ[R] N)
  证明: rfl

@[simp]
-/
theorem domDomCongr_trans (σ₁ : ι ≃ ι') (σ₂ : ι' ≃ ι'') (f : M [⋀^ι]->ₗ[R] N) :
    f.domDomCongr (σ₁.trans σ₂) = (f.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl

@[simp]
/--
theorem `domDomCongr_zero` / 定理 `domDomCongr_zero`

English:
theorem domDomCongr_zero
  given: (σ : ι ≃ ι')
  statement: (0 : M [⋀^ι]->ₗ[R] N).domDomCongr σ = 0
  proof: rfl

@[simp]

中文:
定理 domDomCongr_zero
  条件: (σ : ι ≃ ι')
  结论: (0 : M [⋀^ι]->ₗ[R] N).domDomCongr σ = 0
  证明: rfl

@[simp]
-/
theorem domDomCongr_zero (σ : ι ≃ ι') : (0 : M [⋀^ι]->ₗ[R] N).domDomCongr σ = 0 :=
  rfl

@[simp]
/--
theorem `domDomCongr_add` / 定理 `domDomCongr_add`

English:
theorem domDomCongr_add
  given: (σ : ι ≃ ι') (f g : M [⋀^ι]->ₗ[R] N)
  proof: rfl

@[simp]

中文:
定理 domDomCongr_add
  条件: (σ : ι ≃ ι') (f g : M [⋀^ι]->ₗ[R] N)
  证明: rfl

@[simp]
-/
theorem domDomCongr_add (σ : ι ≃ ι') (f g : M [⋀^ι]->ₗ[R] N) :
    (f + g).domDomCongr σ = f.domDomCongr σ + g.domDomCongr σ :=
  rfl

@[simp]
/--
theorem `domDomCongr_smul` / 定理 `domDomCongr_smul`

English:
theorem domDomCongr_smul
  statement: {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]
  proof: rfl

中文:
定理 domDomCongr_smul
  结论: {S : 类型} [幺半群 S] [分配乘法作用 S N] [标量交换类 R S N]
  证明: rfl
-/
theorem domDomCongr_smul {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]
    (σ : ι ≃ ι') (c : S) (f : M [⋀^ι]->ₗ[R] N) :
    (c • f).domDomCongr σ = c • f.domDomCongr σ :=
  rfl

/-- `AlternatingMap.domDomCongr` as an equivalence.

This is declared separately because it does not work with dot notation. -/
@[simps apply symm_apply]
/--
Definition of `domDomCongrEquiv` / `domDomCongrEquiv` 的定义

English:
definition domDomCongrEquiv
  signature: (σ : ι ≃ ι')
  body: domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv f := by
    ext
    simp [Function.comp_def]
  right_inv m := by
    ext
    simp [Function.comp_def]
  map_add' := domDomCongr_add σ

中文:
定义 domDomCongrEquiv
  签名: (σ : ι ≃ ι')
  定义体: domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv f := by
    ext
    simp [Function.comp_def]
  right_inv m := by
    ext
    simp [Function.comp_def]
  map_add' := domDomCongr_add σ

Depends on / 依赖: domDomCongr
-/
def domDomCongrEquiv (σ : ι ≃ ι') : M [⋀^ι]->ₗ[R] N ≃+ M [⋀^ι']->ₗ[R] N where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv f := by
    ext
    simp [Function.comp_def]
  right_inv m := by
    ext
    simp [Function.comp_def]
  map_add' := domDomCongr_add σ

section DomDomLcongr

variable (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N]

/-- `AlternatingMap.domDomCongr` as a linear equivalence. -/
@[simps apply symm_apply]
/--
Definition of `domDomCongrₗ` / `domDomCongrₗ` 的定义

English:
definition domDomCongrₗ
  signature: (σ : ι ≃ ι')
  body: domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv f := by ext; simp [Function.comp_def]
  right_inv m := by ext; simp [Function.comp_def]
  map_add' := domDomCongr_add σ
  map_smul' := domDomCongr_smul σ

@[simp]

中文:
定义 domDomCongrₗ
  签名: (σ : ι ≃ ι')
  定义体: domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv f := by ext; simp [Function.comp_def]
  right_inv m := by ext; simp [Function.comp_def]
  map_add' := domDomCongr_add σ
  map_smul' := domDomCongr_smul σ

@[simp]

Depends on / 依赖: domDomCongr
-/
def domDomCongrₗ (σ : ι ≃ ι') : M [⋀^ι]->ₗ[R] N ≃ₗ[S] M [⋀^ι']->ₗ[R] N where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv f := by ext; simp [Function.comp_def]
  right_inv m := by ext; simp [Function.comp_def]
  map_add' := domDomCongr_add σ
  map_smul' := domDomCongr_smul σ

@[simp]
/--
theorem `domDomCongrₗ_refl` / 定理 `domDomCongrₗ_refl`

English:
theorem domDomCongrₗ_refl
  proof: rfl

@[simp]

中文:
定理 domDomCongrₗ_refl
  证明: rfl

@[simp]
-/
theorem domDomCongrₗ_refl :
    (domDomCongrₗ S (Equiv.refl ι) : M [⋀^ι]->ₗ[R] N ≃ₗ[S] M [⋀^ι]->ₗ[R] N) =
      LinearEquiv.refl _ _ :=
  rfl

@[simp]
/--
theorem `domDomCongrₗ_toAddEquiv` / 定理 `domDomCongrₗ_toAddEquiv`

English:
theorem domDomCongrₗ_toAddEquiv
  given: (σ : ι ≃ ι')
  proof: rfl

中文:
定理 domDomCongrₗ_toAddEquiv
  条件: (σ : ι ≃ ι')
  证明: rfl
-/
theorem domDomCongrₗ_toAddEquiv (σ : ι ≃ ι') :
    (↑(domDomCongrₗ S σ : M [⋀^ι]->ₗ[R] N ≃ₗ[S] _) : M [⋀^ι]->ₗ[R] N ≃+ _) =
      domDomCongrEquiv σ :=
  rfl

end DomDomLcongr

/-- The results of applying `domDomCongr` to two maps are equal if and only if those maps are. -/
@[simp]
/--
theorem `domDomCongr_eq_iff` / 定理 `domDomCongr_eq_iff`

English:
theorem domDomCongr_eq_iff
  given: (σ : ι ≃ ι') (f g : M [⋀^ι]->ₗ[R] N)
  proof: (domDomCongrEquiv σ : _ ≃+ M [⋀^ι']->ₗ[R] N).apply_eq_iff_eq

@[simp]

中文:
定理 domDomCongr_eq_iff
  条件: (σ : ι ≃ ι') (f g : M [⋀^ι]->ₗ[R] N)
  证明: (domDomCongrEquiv σ : _ ≃+ M [⋀^ι']->ₗ[R] N).apply_eq_iff_eq

@[simp]

Depends on / 依赖: apply_eq_iff_eq, domDomCongrEquiv
-/
theorem domDomCongr_eq_iff (σ : ι ≃ ι') (f g : M [⋀^ι]->ₗ[R] N) :
    f.domDomCongr σ = g.domDomCongr σ ↔ f = g :=
  (domDomCongrEquiv σ : _ ≃+ M [⋀^ι']->ₗ[R] N).apply_eq_iff_eq

@[simp]
/--
theorem `domDomCongr_eq_zero_iff` / 定理 `domDomCongr_eq_zero_iff`

English:
theorem domDomCongr_eq_zero_iff
  given: (σ : ι ≃ ι') (f : M [⋀^ι]->ₗ[R] N)
  proof: (domDomCongrEquiv σ : M [⋀^ι]->ₗ[R] N ≃+ M [⋀^ι']->ₗ[R] N).map_eq_zero_iff

中文:
定理 domDomCongr_eq_zero_iff
  条件: (σ : ι ≃ ι') (f : M [⋀^ι]->ₗ[R] N)
  证明: (domDomCongrEquiv σ : M [⋀^ι]->ₗ[R] N ≃+ M [⋀^ι']->ₗ[R] N).map_eq_zero_iff

Depends on / 依赖: domDomCongrEquiv, map_eq_zero_iff
-/
theorem domDomCongr_eq_zero_iff (σ : ι ≃ ι') (f : M [⋀^ι]->ₗ[R] N) :
    f.domDomCongr σ = 0 ↔ f = 0 :=
  (domDomCongrEquiv σ : M [⋀^ι]->ₗ[R] N ≃+ M [⋀^ι']->ₗ[R] N).map_eq_zero_iff

/--
theorem `domDomCongr_perm` / 定理 `domDomCongr_perm`

English:
theorem domDomCongr_perm
  given: [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
  proof: AlternatingMap.ext fun v => g.map_perm v σ

@[norm_cast]

中文:
定理 domDomCongr_perm
  条件: [有限类型 ι] [DecidableEq ι] (σ : 等价.置换 ι)
  证明: AlternatingMap.ext fun v => g.map_perm v σ

@[norm_cast]

Depends on / 依赖: AlternatingMap, AlternatingMap.ext, g.map_perm, map_perm
-/
theorem domDomCongr_perm [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) :
    g.domDomCongr σ = Equiv.Perm.sign σ • g :=
  AlternatingMap.ext fun v => g.map_perm v σ

@[norm_cast]
/--
theorem `coe_domDomCongr` / 定理 `coe_domDomCongr`

English:
theorem coe_domDomCongr
  given: (σ : ι ≃ ι')
  proof: MultilinearMap.ext fun _ => rfl

中文:
定理 coe_domDomCongr
  条件: (σ : ι ≃ ι')
  证明: MultilinearMap.ext fun _ => rfl

Depends on / 依赖: MultilinearMap, MultilinearMap.ext
-/
theorem coe_domDomCongr (σ : ι ≃ ι') :
    ↑(f.domDomCongr σ) = (f : MultilinearMap R (fun _ : ι => M) N).domDomCongr σ :=
  MultilinearMap.ext fun _ => rfl

end DomDomCongr

/--
theorem `map_linearDependent` / 定理 `map_linearDependent`

English:
theorem map_linearDependent
  statement: {K M N : Type*} [Ring K] [IsDomain K] [AddCommGroup M] [Module K M]
  proof: by
  obtain ⟨s, g, h, i, hi, hz⟩ := not_linearIndependent_iff.mp h
  let := Classical.decEq ι
  suffices f (update v i (g i • v i)) = 0 by
    rw [f.map_update_smul]; rw [Function.update_eq_self]; rw [smul_eq_zero] at this
    exact Or.resolve_left this hz
  rw [← Finset.insert_erase hi]; rw [Finset

中文:
定理 map_linearDependent
  结论: {K M N : 类型} [环 K] [是整环 K] [加法交换群 M] [模 K M]
  证明: by
  obtain ⟨s, g, h, i, hi, hz⟩ := not_linearIndependent_iff.mp h
  let := Classical.decEq ι
  suffices f (update v i (g i • v i)) = 0 by
    rw [f.map_update_smul]; rw [Function.update_eq_self]; rw [smul_eq_zero] at this
    exact Or.resolve_left this hz
  rw [← Finset.insert_erase hi]; rw [Finset

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.insert_erase, Finset.mem_erase.mp, Finset.sum_eq_zero, Finset.sum_insert, Function, Function.update_eq_self, Or.resolve_left, add_eq_zero_iff_eq_neg, f.map_update_neg, f.map_update_smul, f.map_update_sum, insert_erase, map_update_neg, map_update_smul, map_update_sum, mem_erase, neg_eq_zero
-/
theorem map_linearDependent {K M N : Type*} [Ring K] [IsDomain K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [IsTorsionFree K N] (f : M [⋀^ι]->ₗ[K] N)
    (v : ι -> M) (h : ¬LinearIndependent K v) : f v = 0 := by
  obtain ⟨s, g, h, i, hi, hz⟩ := not_linearIndependent_iff.mp h
  let := Classical.decEq ι
  suffices f (update v i (g i • v i)) = 0 by
    rw [f.map_update_smul]; rw [Function.update_eq_self]; rw [smul_eq_zero] at this
    exact Or.resolve_left this hz
  rw [← Finset.insert_erase hi]; rw [Finset.sum_insert (s.notMem_erase i)]; rw [add_eq_zero_iff_eq_neg] at h
  rw [h]; rw [f.map_update_neg]; rw [f.map_update_sum]; rw [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨hij, _⟩ := Finset.mem_erase.mp hj
  rw [f.map_update_smul]; rw [f.map_update_self _ hij.symm]; rw [smul_zero]

section Fin

open Fin

/--
theorem `map_vecCons_add` / 定理 `map_vecCons_add`

English:
theorem map_vecCons_add
  given: {n : Nat} (f : M [⋀^Fin n.succ]->ₗ[R] N) (m : Fin n -> M) (x y : M)
  proof: f.toMultilinearMap.cons_add _ _ _

中文:
定理 map_vecCons_add
  条件: {n : 自然数} (f : M [⋀^有限集 n.succ]->ₗ[R] N) (m : 有限集 n -> M) (x y : M)
  证明: f.toMultilinearMap.cons_add _ _ _

Depends on / 依赖: cons_add, f.toMultilinearMap.cons_add, toMultilinearMap
-/
theorem map_vecCons_add {n : Nat} (f : M [⋀^Fin n.succ]->ₗ[R] N) (m : Fin n -> M) (x y : M) :
    f (Matrix.vecCons (x + y) m) = f (Matrix.vecCons x m) + f (Matrix.vecCons y m) :=
  f.toMultilinearMap.cons_add _ _ _

/--
theorem `map_vecCons_smul` / 定理 `map_vecCons_smul`

English:
theorem map_vecCons_smul
  statement: {n : Nat} (f : M [⋀^Fin n.succ]->ₗ[R] N) (m : Fin n -> M) (c : R)
  proof: f.toMultilinearMap.cons_smul _ _ _

中文:
定理 map_vecCons_smul
  结论: {n : 自然数} (f : M [⋀^有限集 n.succ]->ₗ[R] N) (m : 有限集 n -> M) (c : R)
  证明: f.toMultilinearMap.cons_smul _ _ _

Depends on / 依赖: cons_smul, f.toMultilinearMap.cons_smul, toMultilinearMap
-/
theorem map_vecCons_smul {n : Nat} (f : M [⋀^Fin n.succ]->ₗ[R] N) (m : Fin n -> M) (c : R)
    (x : M) : f (Matrix.vecCons (c • x) m) = c • f (Matrix.vecCons x m) :=
  f.toMultilinearMap.cons_smul _ _ _

end Fin

end AlternatingMap

namespace MultilinearMap

open Equiv

variable [Fintype ι] [DecidableEq ι]

/--
theorem `alternization_map_eq_zero_of_eq_aux` / 定理 `alternization_map_eq_zero_of_eq_aux`

English:
theorem alternization_map_eq_zero_of_eq_aux
  statement: (m : MultilinearMap R (fun _ : ι => M) N')
  proof: by
  rw [sum_apply]
  exact
    Finset.sum_involution (fun σ _ => swap i j * σ)
      (fun σ _ => by simp [Perm.sign_swap i_ne_j, apply_swap_eq_self hv])
      (fun σ _ _ => (not_congr swap_mul_eq_iff).mpr i_ne_j) (fun σ _ => Finset.mem_univ _)
      fun σ _ => swap_mul_involutive i j σ

中文:
定理 alternization_map_eq_zero_of_eq_aux
  结论: (m : 多重线性映射 R (fun _ : ι => M) N')
  证明: by
  rw [sum_apply]
  exact
    Finset.sum_involution (fun σ _ => swap i j * σ)
      (fun σ _ => by simp [Perm.sign_swap i_ne_j, apply_swap_eq_self hv])
      (fun σ _ _ => (not_congr swap_mul_eq_iff).mpr i_ne_j) (fun σ _ => Finset.mem_univ _)
      fun σ _ => swap_mul_involutive i j σ
-/
private theorem alternization_map_eq_zero_of_eq_aux (m : MultilinearMap R (fun _ : ι => M) N')
    (v : ι -> M) (i j : ι) (i_ne_j : i != j) (hv : v i = v j) :
    (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ) v = 0 := by
  rw [sum_apply]
  exact
    Finset.sum_involution (fun σ _ => swap i j * σ)
      (fun σ _ => by simp [Perm.sign_swap i_ne_j, apply_swap_eq_self hv])
      (fun σ _ _ => (not_congr swap_mul_eq_iff).mpr i_ne_j) (fun σ _ => Finset.mem_univ _)
      fun σ _ => swap_mul_involutive i j σ

/--
Definition of `alternatization` / `alternatization` 的定义

English:
definition alternatization
  signature: : MultilinearMap R (fun _ : ι => M) N' ->+ M [⋀^ι]->ₗ[R] N' where
  body: { ∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ with
      toFun := ⇑(∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ)
      map_eq_zero_of_eq' := private fun v i j hvij hij =>
        alternization_map_eq_zero_of_eq_aux m v i j hij hvij }
  map_add' a b := by ext; simp [Finset.sum_add_distrib

中文:
定义 alternatization
  签名: : 多重线性映射 R (fun _ : ι => M) N' ->+ M [⋀^ι]->ₗ[R] N' where
  定义体: { ∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ with
      toFun := ⇑(∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ)
      map_eq_zero_of_eq' := private fun v i j hvij hij =>
        alternization_map_eq_zero_of_eq_aux m v i j hij hvij }
  map_add' a b := by ext; simp [Finset.sum_add_distrib

Depends on / 依赖: Equiv.Perm.sign, Finset, Finset.sum_add_distrib, alternization_map_eq_zero_of_eq_aux, domDomCongr, m.domDomCongr, map_add, map_eq_zero_of_eq, map_zero, private, sum_add_distrib
-/
def alternatization : MultilinearMap R (fun _ : ι => M) N' ->+ M [⋀^ι]->ₗ[R] N' where
  toFun m :=
    { ∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ with
      toFun := ⇑(∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ)
      map_eq_zero_of_eq' := private fun v i j hvij hij =>
        alternization_map_eq_zero_of_eq_aux m v i j hij hvij }
  map_add' a b := by ext; simp [Finset.sum_add_distrib]
  map_zero' := by ext; simp

/--
theorem `alternatization_def` / 定理 `alternatization_def`

English:
theorem alternatization_def
  given: (m : MultilinearMap R (fun _ : ι => M) N')
  proof: rfl

中文:
定理 alternatization_def
  条件: (m : 多重线性映射 R (fun _ : ι => M) N')
  证明: rfl
-/
theorem alternatization_def (m : MultilinearMap R (fun _ : ι => M) N') :
    ⇑(alternatization m) = (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ :) :=
  rfl

/--
theorem `alternatization_coe` / 定理 `alternatization_coe`

English:
theorem alternatization_coe
  given: (m : MultilinearMap R (fun _ : ι => M) N')
  proof: coe_injective rfl

中文:
定理 alternatization_coe
  条件: (m : 多重线性映射 R (fun _ : ι => M) N')
  证明: coe_injective rfl

Depends on / 依赖: coe_injective
-/
theorem alternatization_coe (m : MultilinearMap R (fun _ : ι => M) N') :
    ↑(alternatization m) = (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ :) :=
  coe_injective rfl

/--
theorem `alternatization_apply` / 定理 `alternatization_apply`

English:
theorem alternatization_apply
  given: (m : MultilinearMap R (fun _ : ι => M) N') (v : ι -> M)
  proof: by
  simp only [alternatization_def, smul_apply, sum_apply]

中文:
定理 alternatization_apply
  条件: (m : 多重线性映射 R (fun _ : ι => M) N') (v : ι -> M)
  证明: by
  simp only [alternatization_def, smul_apply, sum_apply]

Depends on / 依赖: alternatization_def, smul_apply, sum_apply
-/
theorem alternatization_apply (m : MultilinearMap R (fun _ : ι => M) N') (v : ι -> M) :
    alternatization m v = ∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ v := by
  simp only [alternatization_def, smul_apply, sum_apply]

end MultilinearMap

namespace AlternatingMap

/--
theorem `coe_alternatization` / 定理 `coe_alternatization`

English:
theorem coe_alternatization
  given: [DecidableEq ι] [Fintype ι] (a : M [⋀^ι]->ₗ[R] N')
  proof: by
  apply AlternatingMap.coe_injective
  simp_rw [MultilinearMap.alternatization_def, ← coe_domDomCongr, domDomCongr_perm, coe_smul,
    smul_smul, Int.units_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    ← coe_multilinearMap, coe_smul]

中文:
定理 coe_alternatization
  条件: [DecidableEq ι] [有限类型 ι] (a : M [⋀^ι]->ₗ[R] N')
  证明: by
  apply AlternatingMap.coe_injective
  simp_rw [MultilinearMap.alternatization_def, ← coe_domDomCongr, domDomCongr_perm, coe_smul,
    smul_smul, Int.units_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    ← coe_multilinearMap, coe_smul]

Depends on / 依赖: AlternatingMap, AlternatingMap.coe_injective, Finset, Finset.card_univ, Finset.sum_const, Fintype, Fintype.card_perm, Int.units_mul_self, MultilinearMap, MultilinearMap.alternatization_def, alternatization_def, card_perm, card_univ, coe_domDomCongr, coe_injective, coe_multilinearMap, coe_smul, domDomCongr_perm, one_smul, simp_rw
-/
theorem coe_alternatization [DecidableEq ι] [Fintype ι] (a : M [⋀^ι]->ₗ[R] N') :
    MultilinearMap.alternatization (a : MultilinearMap R (fun _ => M) N')
    = Nat.factorial (Fintype.card ι) • a := by
  apply AlternatingMap.coe_injective
  simp_rw [MultilinearMap.alternatization_def, ← coe_domDomCongr, domDomCongr_perm, coe_smul,
    smul_smul, Int.units_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    ← coe_multilinearMap, coe_smul]

end AlternatingMap

namespace LinearMap

variable {N'₂ : Type*} [AddCommGroup N'₂] [Module R N'₂] [DecidableEq ι] [Fintype ι]

/--
theorem `compMultilinearMap_alternatization` / 定理 `compMultilinearMap_alternatization`

English:
theorem compMultilinearMap_alternatization
  statement: (g : N' ->ₗ[R] N'₂)
  proof: by
  ext
  simp [MultilinearMap.alternatization_def]

中文:
定理 compMultilinearMap_alternatization
  结论: (g : N' ->ₗ[R] N'₂)
  证明: by
  ext
  simp [MultilinearMap.alternatization_def]

Depends on / 依赖: MultilinearMap, MultilinearMap.alternatization_def, alternatization_def
-/
theorem compMultilinearMap_alternatization (g : N' ->ₗ[R] N'₂)
    (f : MultilinearMap R (fun _ : ι => M) N') :
    MultilinearMap.alternatization (g.compMultilinearMap f)
      = g.compAlternatingMap (MultilinearMap.alternatization f) := by
  ext
  simp [MultilinearMap.alternatization_def]

end LinearMap

section Basis

open AlternatingMap

variable {ι₁ : Type*} [Finite ι]
variable {R' : Type*} {N₁ N₂ : Type*} [CommSemiring R'] [AddCommMonoid N₁] [AddCommMonoid N₂]
variable [Module R' N₁] [Module R' N₂]

/--
theorem `Module.Basis.ext_alternating` / 定理 `Module.Basis.ext_alternating`

English:
theorem Module.Basis.ext_alternating
  statement: {f g : N₁ [⋀^ι]->ₗ[R'] N₂} (e : Basis ι₁ R' N₁)
  proof: by
  refine AlternatingMap.coe_multilinearMap_injective (Basis.ext_multilinear (fun _ => e) fun v => ?_)
  by_cases hi : Function.Injective v
  · exact h v hi
  · have : ¬Function.Injective fun i => e (v i) := hi.imp Function.Injective.of_comp
    rw [coe_multilinearMap]; rw [coe_multilinearMap]; rw

中文:
定理 模.基.ext_alternating
  结论: {f g : N₁ [⋀^ι]->ₗ[R'] N₂} (e : 基 ι₁ R' N₁)
  证明: by
  refine AlternatingMap.coe_multilinearMap_injective (Basis.ext_multilinear (fun _ => e) fun v => ?_)
  by_cases hi : Function.Injective v
  · exact h v hi
  · have : ¬Function.Injective fun i => e (v i) := hi.imp Function.Injective.of_comp
    rw [coe_multilinearMap]; rw [coe_multilinearMap]; rw

Depends on / 依赖: AlternatingMap, AlternatingMap.coe_multilinearMap_injective, Basis.ext_multilinear, Function, Function.Injective, Function.Injective.of_comp, Injective, coe_multilinearMap, coe_multilinearMap_injective, ext_multilinear, f.map_eq_zero_of_not_injective, g.map_eq_zero_of_not_injective, hi.imp, map_eq_zero_of_not_injective, of_comp
-/
theorem Module.Basis.ext_alternating {f g : N₁ [⋀^ι]->ₗ[R'] N₂} (e : Basis ι₁ R' N₁)
    (h : forall v : ι -> ι₁, Function.Injective v -> (f fun i => e (v i)) = g fun i => e (v i)) :
    f = g := by
  refine AlternatingMap.coe_multilinearMap_injective (Basis.ext_multilinear (fun _ => e) fun v => ?_)
  by_cases hi : Function.Injective v
  · exact h v hi
  · have : ¬Function.Injective fun i => e (v i) := hi.imp Function.Injective.of_comp
    rw [coe_multilinearMap]; rw [coe_multilinearMap]; rw [f.map_eq_zero_of_not_injective _ this]; rw [g.map_eq_zero_of_not_injective _ this]

end Basis

variable {R' : Type*} {M'' M₂'' N'' N₂'' : Type*} [CommSemiring R'] [AddCommMonoid M'']
  [AddCommMonoid M₂''] [AddCommMonoid N''] [AddCommMonoid N₂''] [Module R' M''] [Module R' M₂'']
  [Module R' N''] [Module R' N₂'']

/-- An isomorphism of multilinear maps given an isomorphism between their codomains.

This is `Linear.compAlternatingMap` as an isomorphism,
and the alternating version of `LinearEquiv.multilinearMapCongrRight`. -/
@[simps!]
/--
Definition of `LinearEquiv.alternatingMapCongrRight` / `LinearEquiv.alternatingMapCongrRight` 的定义

English:
definition LinearEquiv.alternatingMapCongrRight
  signature: (e : N'' ≃ₗ[R'] N₂'')
  body: e.compAlternatingMap f
  invFun f := e.symm.compAlternatingMap f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

中文:
定义 线性等价.alternatingMapCongrRight
  签名: (e : N'' ≃ₗ[R'] N₂'')
  定义体: e.compAlternatingMap f
  invFun f := e.symm.compAlternatingMap f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

Depends on / 依赖: compAlternatingMap, e.compAlternatingMap
-/
def LinearEquiv.alternatingMapCongrRight (e : N'' ≃ₗ[R'] N₂'') :
    M'' [⋀^ι]->ₗ[R'] N'' ≃ₗ[R'] (M'' [⋀^ι]->ₗ[R'] N₂'') where
  toFun f := e.compAlternatingMap f
  invFun f := e.symm.compAlternatingMap f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- The space of constant maps is equivalent to the space of maps that are alternating with respect
to an empty family. -/
@[simps]
/--
Definition of `AlternatingMap.constLinearEquivOfIsEmpty` / `AlternatingMap.constLinearEquivOfIsEmpty` 的定义

English:
definition AlternatingMap.constLinearEquivOfIsEmpty
  signature: [IsEmpty ι]
  body: AlternatingMap.constOfIsEmpty R' M'' ι
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f 0
right_inv f := ext fun _ => AlternatingMap.congr_arg f Subsingleton.elim _ _

中文:
定义 交错映射.constLinearEquivOfIsEmpty
  签名: [是空 ι]
  定义体: AlternatingMap.constOfIsEmpty R' M'' ι
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f 0
right_inv f := ext fun _ => AlternatingMap.congr_arg f Subsingleton.elim _ _

Depends on / 依赖: AlternatingMap, AlternatingMap.constOfIsEmpty, constOfIsEmpty
-/
def AlternatingMap.constLinearEquivOfIsEmpty [IsEmpty ι] : N'' ≃ₗ[R'] (M'' [⋀^ι]->ₗ[R'] N'') where
  toFun := AlternatingMap.constOfIsEmpty R' M'' ι
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f 0
right_inv f := ext fun _ => AlternatingMap.congr_arg f Subsingleton.elim _ _
