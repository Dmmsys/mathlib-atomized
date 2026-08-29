/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Formal multilinear series

In this file we define `FormalMultilinearSeries 𝕜 E F` to be a family of `n`-multilinear maps for
all `n`, designed to model the sequence of derivatives of a function. In other files we use this
notion to define `C^n` functions (called `contDiff` in `mathlib`) and analytic functions.

## Notation

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

## Tags

multilinear, formal series
-/

@[expose] public section


noncomputable section

open Set Fin Topology

universe u u' v w x y
variable {𝕜 : Type u} {𝕜' : Type u'} {E : Type v} {F : Type w} {G : Type x} {H : Type y}

section

variable [Semiring 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [ContinuousConstSMul 𝕜 F]
  [AddCommMonoid G] [Module 𝕜 G] [TopologicalSpace G] [ContinuousAdd G] [ContinuousConstSMul 𝕜 G]
  [AddCommMonoid H] [Module 𝕜 H] [TopologicalSpace H] [ContinuousAdd H] [ContinuousConstSMul 𝕜 H]

/-- A formal multilinear series over a field `𝕜`, from `E` to `F`, is given by a family of
multilinear maps from `E^n` to `F` for all `n`. -/
@[nolint unusedArguments]
/--
Definition of `FormalMultilinearSeries` / `FormalMultilinearSeries` 的定义

English:
definition FormalMultilinearSeries
  signature: (𝕜 : Type*) (E : Type*) (F : Type*) [Semiring 𝕜] [AddCommMonoid E]
  body: forall n : Nat, E [×n]->L[𝕜] F
deriving Inhabited

中文:
定义 FormalMultilinearSeries
  签名: (𝕜 : 类型) (E : 类型) (F : 类型) [Semiring 𝕜] [AddCommMonoid E]
  定义体: forall n : Nat, E [×n]->L[𝕜] F
deriving Inhabited
-/
def FormalMultilinearSeries (𝕜 : Type*) (E : Type*) (F : Type*) [Semiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]
    [ContinuousConstSMul 𝕜 F] :=
  forall n : Nat, E [×n]->L[𝕜] F
deriving Inhabited

-- This instance exists to avoid an nsmul diamond.
instance (𝕜') [Semiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F] :
    SMul 𝕜' (FormalMultilinearSeries 𝕜 E F) where
  smul k x n := k • x n

section AddCommMonoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (FormalMultilinearSeries 𝕜 E F)
  body: fast_instance% {
  __ := Pi.addCommMonoid
  zero _ := 0
  add x y n := x n + y n }

中文:
实例 :
  签名: AddCommMonoid (FormalMultilinearSeries 𝕜 E F)
  定义体: fast_instance% {
  __ := Pi.addCommMonoid
  zero _ := 0
  add x y n := x n + y n }

Depends on / 依赖: fast_instance
-/
instance : AddCommMonoid (FormalMultilinearSeries 𝕜 E F) := fast_instance% {
  __ := Pi.addCommMonoid
  zero _ := 0
  add x y n := x n + y n }

end AddCommMonoid

section Module

instance (𝕜') [Semiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F] :
    Module 𝕜' (FormalMultilinearSeries 𝕜 E F) :=
inferInstanceAs Module 𝕜' forall n : Nat, E [×n]->L[𝕜] F

end Module

namespace FormalMultilinearSeries

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (n : Nat)
  statement: (0 : FormalMultilinearSeries 𝕜 E F) n = 0
  proof: rfl

@[simp]

中文:
定理 zero_apply
  条件: (n : 自然数)
  结论: (0 : FormalMultilinearSeries 𝕜 E F) n = 0
  证明: rfl

@[simp]
-/
theorem zero_apply (n : Nat) : (0 : FormalMultilinearSeries 𝕜 E F) n = 0 := rfl

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: (p q : FormalMultilinearSeries 𝕜 E F) (n : Nat)
  statement: (p + q) n = p n + q n
  proof: rfl

@[simp]

中文:
定理 add_apply
  条件: (p q : FormalMultilinearSeries 𝕜 E F) (n : 自然数)
  结论: (p + q) n = p n + q n
  证明: rfl

@[simp]
-/
theorem add_apply (p q : FormalMultilinearSeries 𝕜 E F) (n : Nat) : (p + q) n = p n + q n := rfl

@[simp]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  statement: [Semiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F]
  proof: rfl

@[ext]

中文:
定理 smul_apply
  结论: [Semiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F]
  证明: rfl

@[ext]
-/
theorem smul_apply [Semiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F]
    (f : FormalMultilinearSeries 𝕜 E F) (n : Nat) (a : 𝕜') : (a • f) n = a • f n := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {p q : FormalMultilinearSeries 𝕜 E F} (h : forall n, p n = q n)
  statement: p = q
  proof: funext h

中文:
定理 ext
  条件: {p q : FormalMultilinearSeries 𝕜 E F} (h : 对任意 n, p n = q n)
  结论: p = q
  证明: funext h
-/
protected theorem ext {p q : FormalMultilinearSeries 𝕜 E F} (h : forall n, p n = q n) : p = q :=
  funext h

/--
theorem `ne_iff` / 定理 `ne_iff`

English:
theorem ne_iff
  given: {p q : FormalMultilinearSeries 𝕜 E F}
  statement: p != q ↔ exists n, p n != q n
  proof: Function.ne_iff

中文:
定理 ne_iff
  条件: {p q : FormalMultilinearSeries 𝕜 E F}
  结论: p != q ↔ 存在 n, p n != q n
  证明: Function.ne_iff
-/
protected theorem ne_iff {p q : FormalMultilinearSeries 𝕜 E F} : p != q ↔ exists n, p n != q n :=
  Function.ne_iff

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (p : FormalMultilinearSeries 𝕜 E F) (q : FormalMultilinearSeries 𝕜 E G)

中文:
定义 prod
  签名: (p : FormalMultilinearSeries 𝕜 E F) (q : FormalMultilinearSeries 𝕜 E G)
-/
def prod (p : FormalMultilinearSeries 𝕜 E F) (q : FormalMultilinearSeries 𝕜 E G) :
    FormalMultilinearSeries 𝕜 E (F × G)
  | n => (p n).prod (q n)

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: {ι : Type*} {F : ι -> Type*}

中文:
定义 pi
  签名: {ι : 类型} {F : ι -> 类型}
-/
@[simp] def pi {ι : Type*} {F : ι -> Type*}
    [forall i, AddCommGroup (F i)] [forall i, Module 𝕜 (F i)] [forall i, TopologicalSpace (F i)]
    [forall i, IsTopologicalAddGroup (F i)] [forall i, ContinuousConstSMul 𝕜 (F i)]
    (p : Π i, FormalMultilinearSeries 𝕜 E (F i)) :
    FormalMultilinearSeries 𝕜 E (Π i, F i)
  | n => ContinuousMultilinearMap.pi (fun i => p i n)

/--
Definition of `removeZero` / `removeZero` 的定义

English:
definition removeZero
  signature: (p : FormalMultilinearSeries 𝕜 E F)

中文:
定义 removeZero
  签名: (p : FormalMultilinearSeries 𝕜 E F)
-/
def removeZero (p : FormalMultilinearSeries 𝕜 E F) : FormalMultilinearSeries 𝕜 E F
  | 0 => 0
  | n + 1 => p (n + 1)

@[simp]
/--
theorem `removeZero_coeff_zero` / 定理 `removeZero_coeff_zero`

English:
theorem removeZero_coeff_zero
  given: (p : FormalMultilinearSeries 𝕜 E F)
  statement: p.removeZero 0 = 0
  proof: rfl

@[simp]

中文:
定理 removeZero_coeff_zero
  条件: (p : FormalMultilinearSeries 𝕜 E F)
  结论: p.removeZero 0 = 0
  证明: rfl

@[simp]
-/
theorem removeZero_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) : p.removeZero 0 = 0 :=
  rfl

@[simp]
/--
theorem `removeZero_coeff_succ` / 定理 `removeZero_coeff_succ`

English:
theorem removeZero_coeff_succ
  given: (p : FormalMultilinearSeries 𝕜 E F) (n : Nat)
  proof: rfl

中文:
定理 removeZero_coeff_succ
  条件: (p : FormalMultilinearSeries 𝕜 E F) (n : 自然数)
  证明: rfl
-/
theorem removeZero_coeff_succ (p : FormalMultilinearSeries 𝕜 E F) (n : Nat) :
    p.removeZero (n + 1) = p (n + 1) :=
  rfl

/--
theorem `removeZero_of_pos` / 定理 `removeZero_of_pos`

English:
theorem removeZero_of_pos
  given: (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (h : 0 < n)
  proof: by
  rw [← Nat.succ_pred_eq_of_pos h]
  rfl

中文:
定理 removeZero_of_pos
  条件: (p : FormalMultilinearSeries 𝕜 E F) {n : 自然数} (h : 0 < n)
  证明: by
  rw [← Nat.succ_pred_eq_of_pos h]
  rfl

Depends on / 依赖: Nat.succ_pred_eq_of_pos, succ_pred_eq_of_pos
-/
theorem removeZero_of_pos (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (h : 0 < n) :
    p.removeZero n = p n := by
  rw [← Nat.succ_pred_eq_of_pos h]
  rfl

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  statement: (p : FormalMultilinearSeries 𝕜 E F) {m n : Nat} {v : Fin m -> E} {w : Fin n -> E}
  proof: by
  subst n
  congr with ⟨i, hi⟩
  exact h2 i hi hi

中文:
定理 congr
  结论: (p : FormalMultilinearSeries 𝕜 E F) {m n : 自然数} {v : Fin m -> E} {w : Fin n -> E}
  证明: by
  subst n
  congr with ⟨i, hi⟩
  exact h2 i hi hi
-/
theorem congr (p : FormalMultilinearSeries 𝕜 E F) {m n : Nat} {v : Fin m -> E} {w : Fin n -> E}
    (h1 : m = n) (h2 : forall (i : Nat) (him : i < m) (hin : i < n), v ⟨i, him⟩ = w ⟨i, hin⟩) :
    p m v = p n w := by
  subst n
  congr with ⟨i, hi⟩
  exact h2 i hi hi

/--
lemma `congr_zero` / 引理 `congr_zero`

English:
lemma congr_zero
  given: (p : FormalMultilinearSeries 𝕜 E F) {k l : Nat} (h : k = l) (h' : p k = 0)
  proof: by
  subst h; exact h'

中文:
引理 congr_zero
  条件: (p : FormalMultilinearSeries 𝕜 E F) {k l : 自然数} (h : k = l) (h' : p k = 0)
  证明: by
  subst h; exact h'
-/
lemma congr_zero (p : FormalMultilinearSeries 𝕜 E F) {k l : Nat} (h : k = l) (h' : p k = 0) :
    p l = 0 := by
  subst h; exact h'

/--
Definition of `compContinuousLinearMap` / `compContinuousLinearMap` 的定义

English:
definition compContinuousLinearMap
  signature: (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F)
  body: fun n => (p n).compContinuousLinearMap fun _ : Fin n => u

@[simp]

中文:
定义 compContinuousLinearMap
  签名: (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F)
  定义体: fun n => (p n).compContinuousLinearMap fun _ : Fin n => u

@[simp]

Depends on / 依赖: compContinuousLinearMap
-/
def compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F) :
    FormalMultilinearSeries 𝕜 E G := fun n => (p n).compContinuousLinearMap fun _ : Fin n => u

@[simp]
/--
theorem `compContinuousLinearMap_apply` / 定理 `compContinuousLinearMap_apply`

English:
theorem compContinuousLinearMap_apply
  statement: (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F) (n : Nat)
  proof: rfl

@[simp]

中文:
定理 compContinuousLinearMap_apply
  结论: (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F) (n : 自然数)
  证明: rfl

@[simp]
-/
theorem compContinuousLinearMap_apply (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F) (n : Nat)
    (v : Fin n -> E) : (p.compContinuousLinearMap u) n v = p n (u ∘ v) :=
  rfl

@[simp]
/--
theorem `compContinuousLinearMap_id` / 定理 `compContinuousLinearMap_id`

English:
theorem compContinuousLinearMap_id
  given: (p : FormalMultilinearSeries 𝕜 E F)
  proof: rfl

中文:
定理 compContinuousLinearMap_id
  条件: (p : FormalMultilinearSeries 𝕜 E F)
  证明: rfl
-/
theorem compContinuousLinearMap_id (p : FormalMultilinearSeries 𝕜 E F) :
    p.compContinuousLinearMap (.id _ _) = p :=
  rfl

/--
theorem `compContinuousLinearMap_comp` / 定理 `compContinuousLinearMap_comp`

English:
theorem compContinuousLinearMap_comp
  statement: (p : FormalMultilinearSeries 𝕜 G H) (u₁ : F ->L[𝕜] G)
  proof: rfl

中文:
定理 compContinuousLinearMap_comp
  结论: (p : FormalMultilinearSeries 𝕜 G H) (u₁ : F ->L[𝕜] G)
  证明: rfl
-/
theorem compContinuousLinearMap_comp (p : FormalMultilinearSeries 𝕜 G H) (u₁ : F ->L[𝕜] G)
    (u₂ : E ->L[𝕜] F) :
    (p.compContinuousLinearMap u₁).compContinuousLinearMap u₂ =
    p.compContinuousLinearMap (u₁.comp u₂) :=
  rfl

variable (𝕜) [Semiring 𝕜'] [SMul 𝕜 𝕜']
variable [Module 𝕜' E] [ContinuousConstSMul 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
variable [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

/-- Reinterpret a formal `𝕜'`-multilinear series as a formal `𝕜`-multilinear series. -/
@[simp]
/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (p : FormalMultilinearSeries 𝕜' E F)
  body: fun n => (p n).restrictScalars 𝕜

中文:
定义 restrictScalars
  签名: (p : FormalMultilinearSeries 𝕜' E F)
  定义体: fun n => (p n).restrictScalars 𝕜
-/
protected def restrictScalars (p : FormalMultilinearSeries 𝕜' E F) :
    FormalMultilinearSeries 𝕜 E F := fun n => (p n).restrictScalars 𝕜

end FormalMultilinearSeries

end

namespace FormalMultilinearSeries
variable [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousConstSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (FormalMultilinearSeries 𝕜 E F)
  body: inferInstanceAs AddCommGroup forall n : Nat, E [×n]->L[𝕜] F

@[simp]

中文:
实例 :
  签名: AddCommGroup (FormalMultilinearSeries 𝕜 E F)
  定义体: inferInstanceAs AddCommGroup forall n : Nat, E [×n]->L[𝕜] F

@[simp]

Depends on / 依赖: AddCommGroup
-/
instance : AddCommGroup (FormalMultilinearSeries 𝕜 E F) :=
inferInstanceAs AddCommGroup forall n : Nat, E [×n]->L[𝕜] F

@[simp]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: (f : FormalMultilinearSeries 𝕜 E F) (n : Nat)
  statement: (-f) n = - f n
  proof: rfl

@[simp]

中文:
定理 neg_apply
  条件: (f : FormalMultilinearSeries 𝕜 E F) (n : 自然数)
  结论: (-f) n = - f n
  证明: rfl

@[simp]
-/
theorem neg_apply (f : FormalMultilinearSeries 𝕜 E F) (n : Nat) : (-f) n = - f n := rfl

@[simp]
/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: (f g : FormalMultilinearSeries 𝕜 E F) (n : Nat)
  statement: (f - g) n = f n - g n
  proof: rfl

中文:
定理 sub_apply
  条件: (f g : FormalMultilinearSeries 𝕜 E F) (n : 自然数)
  结论: (f - g) n = f n - g n
  证明: rfl
-/
theorem sub_apply (f g : FormalMultilinearSeries 𝕜 E F) (n : Nat) : (f - g) n = f n - g n := rfl

end FormalMultilinearSeries

namespace FormalMultilinearSeries

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

variable (p : FormalMultilinearSeries 𝕜 E F)

/--
Definition of `shift` / `shift` 的定义

English:
definition shift
  signature: : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)
  body: fun n => (p n.succ).curryRight

中文:
定义 shift
  签名: : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)
  定义体: fun n => (p n.succ).curryRight

Depends on / 依赖: curryRight, n.succ
-/
def shift : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F) := fun n => (p n.succ).curryRight

/--
Definition of `unshift` / `unshift` 的定义

English:
definition unshift
  signature: (q : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)) (z : F)

中文:
定义 unshift
  签名: (q : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)) (z : F)
-/
def unshift (q : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)) (z : F) : FormalMultilinearSeries 𝕜 E F
  | 0 => (continuousMultilinearCurryFin0 𝕜 E F).symm z
  | n + 1 => (continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm (q n)

/--
theorem `unshift_shift` / 定理 `unshift_shift`

English:
theorem unshift_shift
  given: {p : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)} {z : F}
  proof: by
  ext1 n
  simp only [shift, Nat.succ_eq_add_one, unshift]
  exact LinearIsometryEquiv.apply_symm_apply (continuousMultilinearCurryRightEquiv' 𝕜 n E F) (p n)

中文:
定理 unshift_shift
  条件: {p : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)} {z : F}
  证明: by
  ext1 n
  simp only [shift, Nat.succ_eq_add_one, unshift]
  exact LinearIsometryEquiv.apply_symm_apply (continuousMultilinearCurryRightEquiv' 𝕜 n E F) (p n)

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.apply_symm_apply, Nat.succ_eq_add_one, apply_symm_apply, continuousMultilinearCurryRightEquiv, succ_eq_add_one, unshift
-/
theorem unshift_shift {p : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)} {z : F} :
    (p.unshift z).shift = p := by
  ext1 n
  simp only [shift, Nat.succ_eq_add_one, unshift]
  exact LinearIsometryEquiv.apply_symm_apply (continuousMultilinearCurryRightEquiv' 𝕜 n E F) (p n)

end FormalMultilinearSeries

section

variable [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousConstSMul 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
  [ContinuousAdd F] [ContinuousConstSMul 𝕜 F] [AddCommMonoid G] [Module 𝕜 G]
  [TopologicalSpace G] [ContinuousAdd G] [ContinuousConstSMul 𝕜 G]

namespace ContinuousLinearMap

/--
Definition of `compFormalMultilinearSeries` / `compFormalMultilinearSeries` 的定义

English:
definition compFormalMultilinearSeries
  signature: (f : F ->L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F)
  body: fun n => f.compContinuousMultilinearMap (p n)

@[simp]

中文:
定义 compFormalMultilinearSeries
  签名: (f : F ->L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F)
  定义体: fun n => f.compContinuousMultilinearMap (p n)

@[simp]

Depends on / 依赖: compContinuousMultilinearMap, f.compContinuousMultilinearMap
-/
def compFormalMultilinearSeries (f : F ->L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G := fun n => f.compContinuousMultilinearMap (p n)

@[simp]
/--
theorem `compFormalMultilinearSeries_apply` / 定理 `compFormalMultilinearSeries_apply`

English:
theorem compFormalMultilinearSeries_apply
  statement: (f : F ->L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F)
  proof: rfl

中文:
定理 compFormalMultilinearSeries_apply
  结论: (f : F ->L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F)
  证明: rfl
-/
theorem compFormalMultilinearSeries_apply (f : F ->L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F)
    (n : Nat) : (f.compFormalMultilinearSeries p) n = f.compContinuousMultilinearMap (p n) :=
  rfl

/--
theorem `compFormalMultilinearSeries_apply'` / 定理 `compFormalMultilinearSeries_apply'`

English:
theorem compFormalMultilinearSeries_apply'
  statement: (f : F ->L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F)
  proof: rfl

中文:
定理 compFormalMultilinearSeries_apply'
  结论: (f : F ->L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F)
  证明: rfl
-/
theorem compFormalMultilinearSeries_apply' (f : F ->L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F)
    (n : Nat) (v : Fin n -> E) : (f.compFormalMultilinearSeries p) n v = f (p n v) :=
  rfl

end ContinuousLinearMap

namespace ContinuousMultilinearMap

variable {ι : Type*} {E : ι -> Type*} [forall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)]
  [forall i, TopologicalSpace (E i)] [forall i, IsTopologicalAddGroup (E i)]
  [forall i, ContinuousConstSMul 𝕜 (E i)] [Fintype ι] (f : ContinuousMultilinearMap 𝕜 E F)

/--
Definition of `toFormalMultilinearSeries` / `toFormalMultilinearSeries` 的定义

English:
definition toFormalMultilinearSeries
  signature: : FormalMultilinearSeries 𝕜 (forall i, E i) F
  body: fun n => if h : Fintype.card ι = n then
    (f.compContinuousLinearMap .proj).domDomCongr (Fintype.equivFinOfCardEq h)
  else 0

中文:
定义 toFormalMultilinearSeries
  签名: : FormalMultilinearSeries 𝕜 (对任意 i, E i) F
  定义体: fun n => if h : Fintype.card ι = n then
    (f.compContinuousLinearMap .proj).domDomCongr (Fintype.equivFinOfCardEq h)
  else 0

Depends on / 依赖: Fintype, Fintype.card, Fintype.equivFinOfCardEq, compContinuousLinearMap, domDomCongr, equivFinOfCardEq, f.compContinuousLinearMap
-/
noncomputable def toFormalMultilinearSeries : FormalMultilinearSeries 𝕜 (forall i, E i) F :=
  fun n => if h : Fintype.card ι = n then
    (f.compContinuousLinearMap .proj).domDomCongr (Fintype.equivFinOfCardEq h)
  else 0

end ContinuousMultilinearMap

end

namespace FormalMultilinearSeries

section Order

variable [Semiring 𝕜] {n : Nat} [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousConstSMul 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
  [TopologicalSpace F] [ContinuousAdd F] [ContinuousConstSMul 𝕜 F]
  {p : FormalMultilinearSeries 𝕜 E F}

/--
Definition of `order` / `order` 的定义

English:
definition order
  signature: (p : FormalMultilinearSeries 𝕜 E F)
  body: sInf { n | p n != 0 }

@[simp]

中文:
定义 order
  签名: (p : FormalMultilinearSeries 𝕜 E F)
  定义体: sInf { n | p n != 0 }

@[simp]
-/
noncomputable def order (p : FormalMultilinearSeries 𝕜 E F) : Nat :=
  sInf { n | p n != 0 }

@[simp]
/--
theorem `order_zero` / 定理 `order_zero`

English:
theorem order_zero
  statement: (0 : FormalMultilinearSeries 𝕜 E F).order = 0
  proof: by simp [order]

中文:
定理 order_zero
  结论: (0 : FormalMultilinearSeries 𝕜 E F).order = 0
  证明: by simp [order]
-/
theorem order_zero : (0 : FormalMultilinearSeries 𝕜 E F).order = 0 := by simp [order]

/--
theorem `ne_zero_of_order_ne_zero` / 定理 `ne_zero_of_order_ne_zero`

English:
theorem ne_zero_of_order_ne_zero
  given: (hp : p.order != 0)
  statement: p != 0
  proof: fun h => by simp [h] at hp

中文:
定理 ne_zero_of_order_ne_zero
  条件: (hp : p.order != 0)
  结论: p != 0
  证明: fun h => by simp [h] at hp
-/
theorem ne_zero_of_order_ne_zero (hp : p.order != 0) : p != 0 := fun h => by simp [h] at hp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `order_eq_find` / 定理 `order_eq_find`

English:
theorem order_eq_find
  given: [DecidablePred fun n => p n != 0] (hp : exists n, p n != 0)
  proof: by convert! Nat.sInf_def hp

中文:
定理 order_eq_find
  条件: [DecidablePred fun n => p n != 0] (hp : 存在 n, p n != 0)
  证明: by convert! Nat.sInf_def hp

Depends on / 依赖: Nat.sInf_def, convert, sInf_def
-/
theorem order_eq_find [DecidablePred fun n => p n != 0] (hp : exists n, p n != 0) :
    p.order = Nat.find hp := by convert! Nat.sInf_def hp

/--
theorem `order_eq_find'` / 定理 `order_eq_find'`

English:
theorem order_eq_find'
  given: [DecidablePred fun n => p n != 0] (hp : p != 0)
  proof: order_eq_find _

中文:
定理 order_eq_find'
  条件: [DecidablePred fun n => p n != 0] (hp : p != 0)
  证明: order_eq_find _

Depends on / 依赖: order_eq_find
-/
theorem order_eq_find' [DecidablePred fun n => p n != 0] (hp : p != 0) :
    p.order = Nat.find (FormalMultilinearSeries.ne_iff.mp hp) :=
  order_eq_find _

/--
theorem `order_eq_zero_iff'` / 定理 `order_eq_zero_iff'`

English:
theorem order_eq_zero_iff'
  statement: p.order = 0 ↔ p = 0 ∨ p 0 != 0
  proof: by
  simpa [order, Nat.sInf_eq_zero, FormalMultilinearSeries.ext_iff, eq_empty_iff_forall_notMem]
    using or_comm

中文:
定理 order_eq_zero_iff'
  结论: p.order = 0 ↔ p = 0 ∨ p 0 != 0
  证明: by
  simpa [order, Nat.sInf_eq_zero, FormalMultilinearSeries.ext_iff, eq_empty_iff_forall_notMem]
    using or_comm

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.ext_iff, Nat.sInf_eq_zero, eq_empty_iff_forall_notMem, ext_iff, or_comm, sInf_eq_zero
-/
theorem order_eq_zero_iff' : p.order = 0 ↔ p = 0 ∨ p 0 != 0 := by
  simpa [order, Nat.sInf_eq_zero, FormalMultilinearSeries.ext_iff, eq_empty_iff_forall_notMem]
    using or_comm

/--
theorem `order_eq_zero_iff` / 定理 `order_eq_zero_iff`

English:
theorem order_eq_zero_iff
  given: (hp : p != 0)
  statement: p.order = 0 ↔ p 0 != 0
  proof: by
  simp [order_eq_zero_iff', hp]

中文:
定理 order_eq_zero_iff
  条件: (hp : p != 0)
  结论: p.order = 0 ↔ p 0 != 0
  证明: by
  simp [order_eq_zero_iff', hp]

Depends on / 依赖: order_eq_zero_iff
-/
theorem order_eq_zero_iff (hp : p != 0) : p.order = 0 ↔ p 0 != 0 := by
  simp [order_eq_zero_iff', hp]

/--
theorem `apply_order_ne_zero` / 定理 `apply_order_ne_zero`

English:
theorem apply_order_ne_zero
  given: (hp : p != 0)
  statement: p p.order != 0
  proof: Nat.sInf_mem (FormalMultilinearSeries.ne_iff.1 hp)

中文:
定理 apply_order_ne_zero
  条件: (hp : p != 0)
  结论: p p.order != 0
  证明: Nat.sInf_mem (FormalMultilinearSeries.ne_iff.1 hp)

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.ne_iff, Nat.sInf_mem, ne_iff, sInf_mem
-/
theorem apply_order_ne_zero (hp : p != 0) : p p.order != 0 :=
  Nat.sInf_mem (FormalMultilinearSeries.ne_iff.1 hp)

/--
theorem `apply_order_ne_zero'` / 定理 `apply_order_ne_zero'`

English:
theorem apply_order_ne_zero'
  given: (hp : p.order != 0)
  statement: p p.order != 0
  proof: apply_order_ne_zero (ne_zero_of_order_ne_zero hp)

中文:
定理 apply_order_ne_zero'
  条件: (hp : p.order != 0)
  结论: p p.order != 0
  证明: apply_order_ne_zero (ne_zero_of_order_ne_zero hp)

Depends on / 依赖: apply_order_ne_zero, ne_zero_of_order_ne_zero
-/
theorem apply_order_ne_zero' (hp : p.order != 0) : p p.order != 0 :=
  apply_order_ne_zero (ne_zero_of_order_ne_zero hp)

/--
theorem `apply_eq_zero_of_lt_order` / 定理 `apply_eq_zero_of_lt_order`

English:
theorem apply_eq_zero_of_lt_order
  given: (hp : n < p.order)
  statement: p n = 0
  proof: by_contra Nat.notMem_of_lt_sInf hp

中文:
定理 apply_eq_zero_of_lt_order
  条件: (hp : n < p.order)
  结论: p n = 0
  证明: by_contra Nat.notMem_of_lt_sInf hp

Depends on / 依赖: Nat.notMem_of_lt_sInf, notMem_of_lt_sInf
-/
theorem apply_eq_zero_of_lt_order (hp : n < p.order) : p n = 0 :=
by_contra Nat.notMem_of_lt_sInf hp

end Order

section Coef

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E} {n : Nat} {z : 𝕜} {y : Fin n -> 𝕜}

/--
Definition of `coeff` / `coeff` 的定义

English:
definition coeff
  signature: (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : Nat)
  body: p n 1

中文:
定义 coeff
  签名: (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : 自然数)
  定义体: p n 1
-/
def coeff (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : Nat) : E :=
  p n 1

/--
theorem `mkPiRing_coeff_eq` / 定理 `mkPiRing_coeff_eq`

English:
theorem mkPiRing_coeff_eq
  given: (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : Nat)
  proof: (p n).mkPiRing_apply_one_eq_self

@[simp]

中文:
定理 mkPiRing_coeff_eq
  条件: (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : 自然数)
  证明: (p n).mkPiRing_apply_one_eq_self

@[simp]

Depends on / 依赖: mkPiRing_apply_one_eq_self
-/
theorem mkPiRing_coeff_eq (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : Nat) :
    ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (p.coeff n) = p n :=
  (p n).mkPiRing_apply_one_eq_self

@[simp]
/--
theorem `apply_eq_prod_smul_coeff` / 定理 `apply_eq_prod_smul_coeff`

English:
theorem apply_eq_prod_smul_coeff
  statement: p n y = (∏ i, y i) • p.coeff n
  proof: by
  convert! (p n).toMultilinearMap.map_smul_univ y 1
  simp only [Pi.one_apply, smul_eq_mul, mul_one]

中文:
定理 apply_eq_prod_smul_coeff
  结论: p n y = (∏ i, y i) • p.coeff n
  证明: by
  convert! (p n).toMultilinearMap.map_smul_univ y 1
  simp only [Pi.one_apply, smul_eq_mul, mul_one]

Depends on / 依赖: Pi.one_apply, convert, map_smul_univ, mul_one, one_apply, smul_eq_mul, toMultilinearMap, toMultilinearMap.map_smul_univ
-/
theorem apply_eq_prod_smul_coeff : p n y = (∏ i, y i) • p.coeff n := by
  convert! (p n).toMultilinearMap.map_smul_univ y 1
  simp only [Pi.one_apply, smul_eq_mul, mul_one]

/--
theorem `coeff_eq_zero` / 定理 `coeff_eq_zero`

English:
theorem coeff_eq_zero
  statement: p.coeff n = 0 ↔ p n = 0
  proof: by
  rw [← mkPiRing_coeff_eq p]; rw [ContinuousMultilinearMap.mkPiRing_eq_zero_iff]

中文:
定理 coeff_eq_zero
  结论: p.coeff n = 0 ↔ p n = 0
  证明: by
  rw [← mkPiRing_coeff_eq p]; rw [ContinuousMultilinearMap.mkPiRing_eq_zero_iff]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.mkPiRing_eq_zero_iff, mkPiRing_coeff_eq, mkPiRing_eq_zero_iff
-/
theorem coeff_eq_zero : p.coeff n = 0 ↔ p n = 0 := by
  rw [← mkPiRing_coeff_eq p]; rw [ContinuousMultilinearMap.mkPiRing_eq_zero_iff]

/--
theorem `apply_eq_pow_smul_coeff` / 定理 `apply_eq_pow_smul_coeff`

English:
theorem apply_eq_pow_smul_coeff
  statement: (p n fun _ => z) = z ^ n • p.coeff n
  proof: by simp

@[simp]

中文:
定理 apply_eq_pow_smul_coeff
  结论: (p n fun _ => z) = z ^ n • p.coeff n
  证明: by simp

@[simp]
-/
theorem apply_eq_pow_smul_coeff : (p n fun _ => z) = z ^ n • p.coeff n := by simp

@[simp]
/--
theorem `norm_apply_eq_norm_coef` / 定理 `norm_apply_eq_norm_coef`

English:
theorem norm_apply_eq_norm_coef
  statement: ‖p n‖ = ‖coeff p n‖
  proof: by
  rw [← mkPiRing_coeff_eq p]; rw [ContinuousMultilinearMap.norm_mkPiRing]

中文:
定理 norm_apply_eq_norm_coef
  结论: ‖p n‖ = ‖coeff p n‖
  证明: by
  rw [← mkPiRing_coeff_eq p]; rw [ContinuousMultilinearMap.norm_mkPiRing]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.norm_mkPiRing, mkPiRing_coeff_eq, norm_mkPiRing
-/
theorem norm_apply_eq_norm_coef : ‖p n‖ = ‖coeff p n‖ := by
  rw [← mkPiRing_coeff_eq p]; rw [ContinuousMultilinearMap.norm_mkPiRing]

end Coef

section Fslope

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : FormalMultilinearSeries 𝕜 𝕜 E} {n : Nat}

/--
Definition of `fslope` / `fslope` 的定义

English:
definition fslope
  signature: (p : FormalMultilinearSeries 𝕜 𝕜 E)
  body: fun n => (p (n + 1)).curryLeft 1

@[simp]

中文:
定义 fslope
  签名: (p : FormalMultilinearSeries 𝕜 𝕜 E)
  定义体: fun n => (p (n + 1)).curryLeft 1

@[simp]

Depends on / 依赖: curryLeft
-/
noncomputable def fslope (p : FormalMultilinearSeries 𝕜 𝕜 E) : FormalMultilinearSeries 𝕜 𝕜 E :=
  fun n => (p (n + 1)).curryLeft 1

@[simp]
/--
theorem `coeff_fslope` / 定理 `coeff_fslope`

English:
theorem coeff_fslope
  statement: p.fslope.coeff n = p.coeff (n + 1)
  proof: by
  simp only [fslope, coeff, ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  exact Fin.cons_self_tail (fun _ => (1 : 𝕜))

@[simp]

中文:
定理 coeff_fslope
  结论: p.fslope.coeff n = p.coeff (n + 1)
  证明: by
  simp only [fslope, coeff, ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  exact Fin.cons_self_tail (fun _ => (1 : 𝕜))

@[simp]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail, cons_self_tail, curryLeft_apply, fslope
-/
theorem coeff_fslope : p.fslope.coeff n = p.coeff (n + 1) := by
  simp only [fslope, coeff, ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  exact Fin.cons_self_tail (fun _ => (1 : 𝕜))

@[simp]
/--
theorem `coeff_iterate_fslope` / 定理 `coeff_iterate_fslope`

English:
theorem coeff_iterate_fslope
  given: (k n : Nat)
  statement: (fslope^[k] p).coeff n = p.coeff (n + k)
  proof: by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => simp [ih, add_assoc]

中文:
定理 coeff_iterate_fslope
  条件: (k n : 自然数)
  结论: (fslope^[k] p).coeff n = p.coeff (n + k)
  证明: by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => simp [ih, add_assoc]

Depends on / 依赖: add_assoc, generalizing
-/
theorem coeff_iterate_fslope (k n : Nat) : (fslope^[k] p).coeff n = p.coeff (n + k) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => simp [ih, add_assoc]

end Fslope

end FormalMultilinearSeries

section Const

/--
Definition of `constFormalMultilinearSeries` / `constFormalMultilinearSeries` 的定义

English:
definition constFormalMultilinearSeries
  signature: (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)

中文:
定义 constFormalMultilinearSeries
  签名: (𝕜 : 类型) [NontriviallyNormedField 𝕜] (E : 类型)
-/
def constFormalMultilinearSeries (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ContinuousConstSMul 𝕜 E] [IsTopologicalAddGroup E]
    {F : Type*} [NormedAddCommGroup F] [IsTopologicalAddGroup F] [NormedSpace 𝕜 F]
    [ContinuousConstSMul 𝕜 F] (c : F) : FormalMultilinearSeries 𝕜 E F
  | 0 => ContinuousMultilinearMap.uncurry0 _ _ c
  | _ => 0

@[simp]
/--
theorem `constFormalMultilinearSeries_apply_zero` / 定理 `constFormalMultilinearSeries_apply_zero`

English:
theorem constFormalMultilinearSeries_apply_zero
  statement: [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  proof: rfl

@[simp]

中文:
定理 constFormalMultilinearSeries_apply_zero
  结论: [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  证明: rfl

@[simp]
-/
theorem constFormalMultilinearSeries_apply_zero [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {c : F} :
    constFormalMultilinearSeries 𝕜 E c 0 = ContinuousMultilinearMap.uncurry0 _ _ c :=
  rfl

@[simp]
/--
theorem `constFormalMultilinearSeries_apply_succ` / 定理 `constFormalMultilinearSeries_apply_succ`

English:
theorem constFormalMultilinearSeries_apply_succ
  statement: [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  proof: rfl

中文:
定理 constFormalMultilinearSeries_apply_succ
  结论: [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  证明: rfl
-/
theorem constFormalMultilinearSeries_apply_succ [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {c : F} {n : Nat} :
    constFormalMultilinearSeries 𝕜 E c (n + 1) = 0 :=
  rfl

/--
theorem `constFormalMultilinearSeries_apply_of_nonzero` / 定理 `constFormalMultilinearSeries_apply_of_nonzero`

English:
theorem constFormalMultilinearSeries_apply_of_nonzero
  statement: [NontriviallyNormedField 𝕜]
  proof: Nat.casesOn n (fun hn => (hn rfl).elim) (fun _ _ => rfl) hn

@[simp]

中文:
定理 constFormalMultilinearSeries_apply_of_nonzero
  结论: [NontriviallyNormedField 𝕜]
  证明: Nat.casesOn n (fun hn => (hn rfl).elim) (fun _ _ => rfl) hn

@[simp]

Depends on / 依赖: Nat.casesOn, casesOn
-/
theorem constFormalMultilinearSeries_apply_of_nonzero [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {c : F}
    {n : Nat} (hn : n != 0) : constFormalMultilinearSeries 𝕜 E c n = 0 :=
  Nat.casesOn n (fun hn => (hn rfl).elim) (fun _ _ => rfl) hn

@[simp]
/--
lemma `constFormalMultilinearSeries_zero` / 引理 `constFormalMultilinearSeries_zero`

English:
lemma constFormalMultilinearSeries_zero
  statement: [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  proof: by
  ext n
  induction n <;> simp

@[simp]

中文:
引理 constFormalMultilinearSeries_zero
  结论: [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  证明: by
  ext n
  induction n <;> simp

@[simp]
-/
lemma constFormalMultilinearSeries_zero [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] :
    constFormalMultilinearSeries 𝕜 E (0 : F) = 0 := by
  ext n
  induction n <;> simp

@[simp]
/--
lemma `compContinuousLinearMap_zero` / 引理 `compContinuousLinearMap_zero`

English:
lemma compContinuousLinearMap_zero
  statement: [NontriviallyNormedField 𝕜]
  proof: by
  ext n v
  cases n with
  | zero =>
    simp only [FormalMultilinearSeries.compContinuousLinearMap_apply, Matrix.zero_empty,
      constFormalMultilinearSeries_apply_zero, ContinuousMultilinearMap.uncurry0_apply]
    congr
    apply Subsingleton.allEq
  | succ =>
    simp [FunLike.coe_zero]

中文:
引理 compContinuousLinearMap_zero
  结论: [NontriviallyNormedField 𝕜]
  证明: by
  ext n v
  cases n with
  | zero =>
    simp only [FormalMultilinearSeries.compContinuousLinearMap_apply, Matrix.zero_empty,
      constFormalMultilinearSeries_apply_zero, ContinuousMultilinearMap.uncurry0_apply]
    congr
    apply Subsingleton.allEq
  | succ =>
    simp [FunLike.coe_zero]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.uncurry0_apply, FormalMultilinearSeries, FormalMultilinearSeries.compContinuousLinearMap_apply, FunLike, FunLike.coe_zero, Matrix, Matrix.zero_empty, Subsingleton, Subsingleton.allEq, coe_zero, compContinuousLinearMap_apply, constFormalMultilinearSeries_apply_zero, uncurry0_apply, zero_empty
-/
lemma compContinuousLinearMap_zero [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (p : FormalMultilinearSeries 𝕜 F G) :
    p.compContinuousLinearMap (0 : E ->L[𝕜] F) = constFormalMultilinearSeries 𝕜 E (p 0 0) := by
  ext n v
  cases n with
  | zero =>
    simp only [FormalMultilinearSeries.compContinuousLinearMap_apply, Matrix.zero_empty,
      constFormalMultilinearSeries_apply_zero, ContinuousMultilinearMap.uncurry0_apply]
    congr
    apply Subsingleton.allEq
  | succ =>
    simp [FunLike.coe_zero]

end Const

section Linear

variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousLinearMap

/--
Definition of `fpowerSeries` / `fpowerSeries` 的定义

English:
definition fpowerSeries
  signature: (f : E ->L[𝕜] F) (x : E)

中文:
定义 fpowerSeries
  签名: (f : E ->L[𝕜] F) (x : E)
-/
def fpowerSeries (f : E ->L[𝕜] F) (x : E) : FormalMultilinearSeries 𝕜 E F
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ (f x)
  | 1 => (continuousMultilinearCurryFin1 𝕜 E F).symm f
  | _ => 0

@[simp]
/--
theorem `fpowerSeries_apply_zero` / 定理 `fpowerSeries_apply_zero`

English:
theorem fpowerSeries_apply_zero
  given: (f : E ->L[𝕜] F) (x : E)
  proof: rfl

@[simp]

中文:
定理 fpowerSeries_apply_zero
  条件: (f : E ->L[𝕜] F) (x : E)
  证明: rfl

@[simp]
-/
theorem fpowerSeries_apply_zero (f : E ->L[𝕜] F) (x : E) :
    f.fpowerSeries x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ (f x) :=
  rfl

@[simp]
/--
theorem `fpowerSeries_apply_one` / 定理 `fpowerSeries_apply_one`

English:
theorem fpowerSeries_apply_one
  given: (f : E ->L[𝕜] F) (x : E)
  proof: rfl

@[simp]

中文:
定理 fpowerSeries_apply_one
  条件: (f : E ->L[𝕜] F) (x : E)
  证明: rfl

@[simp]
-/
theorem fpowerSeries_apply_one (f : E ->L[𝕜] F) (x : E) :
    f.fpowerSeries x 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm f :=
  rfl

@[simp]
/--
theorem `fpowerSeries_apply_add_two` / 定理 `fpowerSeries_apply_add_two`

English:
theorem fpowerSeries_apply_add_two
  given: (f : E ->L[𝕜] F) (x : E) (n : Nat)
  statement: f.fpowerSeries x (n + 2) = 0
  proof: rfl

中文:
定理 fpowerSeries_apply_add_two
  条件: (f : E ->L[𝕜] F) (x : E) (n : 自然数)
  结论: f.fpowerSeries x (n + 2) = 0
  证明: rfl
-/
theorem fpowerSeries_apply_add_two (f : E ->L[𝕜] F) (x : E) (n : Nat) : f.fpowerSeries x (n + 2) = 0 :=
  rfl

end ContinuousLinearMap

end Linear
