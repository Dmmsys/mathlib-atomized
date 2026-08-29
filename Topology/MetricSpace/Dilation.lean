/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
module

public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Data.FunLike.Basic

/-!
# Dilations

We define dilations, i.e., maps between emetric spaces that satisfy
`edist (f x) (f y) = r * edist x y` for some `r ∉ {0, ∞}`.

The value `r = 0` is not allowed because we want dilations of (e)metric spaces to be automatically
injective. The value `r = ∞` is not allowed because this way we can define `Dilation.ratio f : ℝ≥0`,
not `Dilation.ratio f : ℝ≥0∞`. Also, we do not often need maps sending distinct points to points at
infinite distance.

## Main definitions

* `Dilation.ratio f : ℝ≥0`: the value of `r` in the relation above, defaulting to 1 in the case
  where it is not well-defined.

## Notation

- `α →ᵈ β`: notation for `Dilation α β`.

## Implementation notes

The type of dilations defined in this file are also referred to as "similarities" or "similitudes"
by other authors. The name `Dilation` was chosen to match the Wikipedia name.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `PseudoEMetricSpace` and we specialize to `PseudoMetricSpace` and `MetricSpace` when
needed.

## TODO

- Introduce dilation equivs.
- Refactor the `Isometry` API to match the `*HomClass` API below.

## References

- https://en.wikipedia.org/wiki/Dilation_(metric_space)
- [Marcel Berger, *Geometry*][berger1987]
-/

@[expose] public section

noncomputable section

open Bornology Function Set Topology Metric
open scoped ENNReal NNReal

section Defs

variable (α : Type*) (β : Type*) [PseudoEMetricSpace α] [PseudoEMetricSpace β]

/--
Definition of `Dilation` / `Dilation` 的定义

English:
structure Dilation
  parameters: where
  axioms and operations (2):
    - toFun : α -> β
    - edist_eq' : exists r : Real>=0, r != 0 ∧ forall x y : α, edist (toFun x) (toFun y) = r * edist x y

中文:
结构 Dilation
  参数: where
  公理与运算 (2 个):
    - toFun : α -> β
    - edist_eq' : 存在 r : 实数>=0, r != 0 ∧ 对任意 x y : α, edist (toFun x) (toFun y) = r * edist x y
-/
structure Dilation where
  /-- The underlying function.

  Do NOT use directly. Use the coercion instead. -/
  toFun : α -> β
  edist_eq' : exists r : Real>=0, r != 0 ∧ forall x y : α, edist (toFun x) (toFun y) = r * edist x y

@[inherit_doc] infixl:25 " ->ᵈ " => Dilation

/--
Definition of `DilationClass` / `DilationClass` 的定义

English:
class DilationClass
  parameters: (F : Type*) (α β : outParam Type*) [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  axioms and operations (1):
    - edist_eq' : forall f : F, exists r : Real>=0, r != 0 ∧ forall x y : α, edist (f x) (f y) = r * edist x y

中文:
类 Dilation类
  参数: (F : 类型) (α β : outParam 类型) [PseudoEMetric空间 α] [PseudoEMetric空间 β]
  公理与运算 (1 个):
    - edist_eq' : 对任意 f : F, 存在 r : 实数>=0, r != 0 ∧ 对任意 x y : α, edist (f x) (f y) = r * edist x y
-/
class DilationClass (F : Type*) (α β : outParam Type*) [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    [FunLike F α β] : Prop where
  edist_eq' : forall f : F, exists r : Real>=0, r != 0 ∧ forall x y : α, edist (f x) (f y) = r * edist x y

end Defs

namespace Dilation

variable {α : Type*} {β : Type*} {γ : Type*} {F : Type*}

section Setup

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β]

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (α ->ᵈ β) α β where
  body: toFun
  coe_injective f g h := by cases f; cases g; congr

中文:
实例 funLike
  签名: : 函数状 (α ->ᵈ β) α β where
  定义体: toFun
  coe_injective f g h := by cases f; cases g; congr
-/
instance funLike : FunLike (α ->ᵈ β) α β where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

/--
Instance `toDilationClass` / 实例 `toDilationClass`

English:
instance toDilationClass
  signature: : DilationClass (α ->ᵈ β) α β where
  body: edist_eq' f

@[simp]

中文:
实例 toDilationClass
  签名: : Dilation类 (α ->ᵈ β) α β where
  定义体: edist_eq' f

@[simp]

Depends on / 依赖: edist_eq
-/
instance toDilationClass : DilationClass (α ->ᵈ β) α β where
  edist_eq' f := edist_eq' f

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : α ->ᵈ β}
  statement: f.toFun = (f : α -> β)
  proof: rfl

@[simp]

中文:
定理 toFun_eq_coe
  条件: {f : α ->ᵈ β}
  结论: f.toFun = (f : α -> β)
  证明: rfl

@[simp]
-/
theorem toFun_eq_coe {f : α ->ᵈ β} : f.toFun = (f : α -> β) :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : α -> β) (h)
  statement: ⇑(⟨f, h⟩ : α ->ᵈ β) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : α -> β) (h)
  结论: ⇑(⟨f, h⟩ : α ->ᵈ β) = f
  证明: rfl
-/
theorem coe_mk (f : α -> β) (h) : ⇑(⟨f, h⟩ : α ->ᵈ β) = f :=
  rfl

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : α ->ᵈ β} (h : f = g) (x : α)
  statement: f x = g x
  proof: DFunLike.congr_fun h x

中文:
定理 congr_fun
  条件: {f g : α ->ᵈ β} (h : f = g) (x : α)
  结论: f x = g x
  证明: DFunLike.congr_fun h x
-/
protected theorem congr_fun {f g : α ->ᵈ β} (h : f = g) (x : α) : f x = g x :=
  DFunLike.congr_fun h x

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: (f : α ->ᵈ β) {x y : α} (h : x = y)
  statement: f x = f y
  proof: DFunLike.congr_arg f h

@[ext]

中文:
定理 congr_arg
  条件: (f : α ->ᵈ β) {x y : α} (h : x = y)
  结论: f x = f y
  证明: DFunLike.congr_arg f h

@[ext]
-/
protected theorem congr_arg (f : α ->ᵈ β) {x y : α} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : α ->ᵈ β} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

@[simp]

中文:
定理 ext
  条件: {f g : α ->ᵈ β} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : α ->ᵈ β} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : α ->ᵈ β) (h)
  statement: Dilation.mk f h = f
  proof: ext fun _ => rfl

中文:
定理 mk_coe
  条件: (f : α ->ᵈ β) (h)
  结论: Dilation.mk f h = f
  证明: ext fun _ => rfl
-/
theorem mk_coe (f : α ->ᵈ β) (h) : Dilation.mk f h = f :=
  ext fun _ => rfl

/-- Copy of a `Dilation` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[simps -fullyApplied]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : α ->ᵈ β) (f' : α -> β) (h : f' = ⇑f)
  body: f'
  edist_eq' := h.symm ▸ f.edist_eq'

中文:
定义 copy
  签名: (f : α ->ᵈ β) (f' : α -> β) (h : f' = ⇑f)
  定义体: f'
  edist_eq' := h.symm ▸ f.edist_eq'
-/
protected def copy (f : α ->ᵈ β) (f' : α -> β) (h : f' = ⇑f) : α ->ᵈ β where
  toFun := f'
  edist_eq' := h.symm ▸ f.edist_eq'

/--
theorem `copy_eq_self` / 定理 `copy_eq_self`

English:
theorem copy_eq_self
  given: (f : α ->ᵈ β) {f' : α -> β} (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq_self
  条件: (f : α ->ᵈ β) {f' : α -> β} (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq_self (f : α ->ᵈ β) {f' : α -> β} (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable [FunLike F α β]

open scoped Classical in
/--
Definition of `ratio` / `ratio` 的定义

English:
definition ratio
  signature: [DilationClass F α β] (f : F)
  body: if forall x y : α, edist x y = 0 ∨ edist x y = ⊤ then 1 else (DilationClass.edist_eq' f).choose

中文:
定义 ratio
  签名: [Dilation类 F α β] (f : F)
  定义体: if forall x y : α, edist x y = 0 ∨ edist x y = ⊤ then 1 else (DilationClass.edist_eq' f).choose

Depends on / 依赖: DilationClass, DilationClass.edist_eq, edist_eq
-/
def ratio [DilationClass F α β] (f : F) : Real>=0 :=
  if forall x y : α, edist x y = 0 ∨ edist x y = ⊤ then 1 else (DilationClass.edist_eq' f).choose

/--
theorem `ratio_of_trivial` / 定理 `ratio_of_trivial`

English:
theorem ratio_of_trivial
  statement: [DilationClass F α β] (f : F)
  proof: if_pos h

@[nontriviality]

中文:
定理 ratio_of_trivial
  结论: [Dilation类 F α β] (f : F)
  证明: if_pos h

@[nontriviality]

Depends on / 依赖: if_pos
-/
theorem ratio_of_trivial [DilationClass F α β] (f : F)
    (h : forall x y : α, edist x y = 0 ∨ edist x y = ∞) : ratio f = 1 :=
  if_pos h

@[nontriviality]
/--
theorem `ratio_of_subsingleton` / 定理 `ratio_of_subsingleton`

English:
theorem ratio_of_subsingleton
  given: [Subsingleton α] [DilationClass F α β] (f : F)
  statement: ratio f = 1
  proof: if_pos fun x y => by simp [Subsingleton.elim x y]

中文:
定理 ratio_of_subsingleton
  条件: [子单例 α] [Dilation类 F α β] (f : F)
  结论: ratio f = 1
  证明: if_pos fun x y => by simp [Subsingleton.elim x y]

Depends on / 依赖: Subsingleton, Subsingleton.elim, if_pos
-/
theorem ratio_of_subsingleton [Subsingleton α] [DilationClass F α β] (f : F) : ratio f = 1 :=
  if_pos fun x y => by simp [Subsingleton.elim x y]

/--
theorem `ratio_ne_zero` / 定理 `ratio_ne_zero`

English:
theorem ratio_ne_zero
  given: [DilationClass F α β] (f : F)
  statement: ratio f != 0
  proof: by
  rw [ratio]; split_ifs
  · exact one_ne_zero
  exact (DilationClass.edist_eq' f).choose_spec.1

中文:
定理 ratio_ne_zero
  条件: [Dilation类 F α β] (f : F)
  结论: ratio f != 0
  证明: by
  rw [ratio]; split_ifs
  · exact one_ne_zero
  exact (DilationClass.edist_eq' f).choose_spec.1

Depends on / 依赖: DilationClass, DilationClass.edist_eq, choose_spec, edist_eq, one_ne_zero, split_ifs
-/
theorem ratio_ne_zero [DilationClass F α β] (f : F) : ratio f != 0 := by
  rw [ratio]; split_ifs
  · exact one_ne_zero
  exact (DilationClass.edist_eq' f).choose_spec.1

/--
theorem `ratio_pos` / 定理 `ratio_pos`

English:
theorem ratio_pos
  given: [DilationClass F α β] (f : F)
  statement: 0 < ratio f
  proof: (ratio_ne_zero f).bot_lt

@[simp]

中文:
定理 ratio_pos
  条件: [Dilation类 F α β] (f : F)
  结论: 0 < ratio f
  证明: (ratio_ne_zero f).bot_lt

@[simp]

Depends on / 依赖: bot_lt, ratio_ne_zero
-/
theorem ratio_pos [DilationClass F α β] (f : F) : 0 < ratio f :=
  (ratio_ne_zero f).bot_lt

@[simp]
/--
theorem `edist_eq` / 定理 `edist_eq`

English:
theorem edist_eq
  given: [DilationClass F α β] (f : F) (x y : α)
  proof: by
  rw [ratio]; split_ifs with key
  · rcases DilationClass.edist_eq' f with ⟨r, hne, hr⟩
    replace hr := hr x y
    rcases key x y with h | h
    · simp only [hr, h, mul_zero]
    · simp [hr, h, hne]
  exact (DilationClass.edist_eq' f).choose_spec.2 x y

@[simp]

中文:
定理 edist_eq
  条件: [Dilation类 F α β] (f : F) (x y : α)
  证明: by
  rw [ratio]; split_ifs with key
  · rcases DilationClass.edist_eq' f with ⟨r, hne, hr⟩
    replace hr := hr x y
    rcases key x y with h | h
    · simp only [hr, h, mul_zero]
    · simp [hr, h, hne]
  exact (DilationClass.edist_eq' f).choose_spec.2 x y

@[simp]

Depends on / 依赖: DilationClass, DilationClass.edist_eq, choose_spec, edist_eq, mul_zero, replace, split_ifs
-/
theorem edist_eq [DilationClass F α β] (f : F) (x y : α) :
    edist (f x) (f y) = ratio f * edist x y := by
  rw [ratio]; split_ifs with key
  · rcases DilationClass.edist_eq' f with ⟨r, hne, hr⟩
    replace hr := hr x y
    rcases key x y with h | h
    · simp only [hr, h, mul_zero]
    · simp [hr, h, hne]
  exact (DilationClass.edist_eq' f).choose_spec.2 x y

@[simp]
/--
theorem `nndist_eq` / 定理 `nndist_eq`

English:
theorem nndist_eq
  statement: {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β]
  proof: by
  simp only [← ENNReal.coe_inj, ← edist_nndist, ENNReal.coe_mul, edist_eq]

@[simp]

中文:
定理 nndist_eq
  结论: {α β F : 类型} [伪度量空间 α] [伪度量空间 β] [函数状 F α β]
  证明: by
  simp only [← ENNReal.coe_inj, ← edist_nndist, ENNReal.coe_mul, edist_eq]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_inj, ENNReal.coe_mul, coe_inj, coe_mul, edist_eq, edist_nndist
-/
theorem nndist_eq {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β]
    [DilationClass F α β] (f : F) (x y : α) :
    nndist (f x) (f y) = ratio f * nndist x y := by
  simp only [← ENNReal.coe_inj, ← edist_nndist, ENNReal.coe_mul, edist_eq]

@[simp]
/--
theorem `dist_eq` / 定理 `dist_eq`

English:
theorem dist_eq
  statement: {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β]
  proof: by
  simp only [dist_nndist, nndist_eq, NNReal.coe_mul]

中文:
定理 dist_eq
  结论: {α β F : 类型} [伪度量空间 α] [伪度量空间 β] [函数状 F α β]
  证明: by
  simp only [dist_nndist, nndist_eq, NNReal.coe_mul]

Depends on / 依赖: NNReal, NNReal.coe_mul, coe_mul, dist_nndist, nndist_eq
-/
theorem dist_eq {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β]
    [DilationClass F α β] (f : F) (x y : α) :
    dist (f x) (f y) = ratio f * dist x y := by
  simp only [dist_nndist, nndist_eq, NNReal.coe_mul]

/--
theorem `ratio_unique` / 定理 `ratio_unique`

English:
theorem ratio_unique
  statement: [DilationClass F α β] {f : F} {x y : α} {r : Real>=0} (h₀ : edist x y != 0)
  proof: by
  simpa only [hr, ENNReal.mul_left_inj h₀ htop, ENNReal.coe_inj] using edist_eq f x y

中文:
定理 ratio_unique
  结论: [Dilation类 F α β] {f : F} {x y : α} {r : 实数>=0} (h₀ : edist x y != 0)
  证明: by
  simpa only [hr, ENNReal.mul_left_inj h₀ htop, ENNReal.coe_inj] using edist_eq f x y

Depends on / 依赖: ENNReal, ENNReal.coe_inj, ENNReal.mul_left_inj, coe_inj, edist_eq, mul_left_inj
-/
theorem ratio_unique [DilationClass F α β] {f : F} {x y : α} {r : Real>=0} (h₀ : edist x y != 0)
    (htop : edist x y != ⊤) (hr : edist (f x) (f y) = r * edist x y) : r = ratio f := by
  simpa only [hr, ENNReal.mul_left_inj h₀ htop, ENNReal.coe_inj] using edist_eq f x y

/--
theorem `ratio_unique_of_nndist_ne_zero` / 定理 `ratio_unique_of_nndist_ne_zero`

English:
theorem ratio_unique_of_nndist_ne_zero
  statement: {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
  proof: ratio_unique (by rwa [edist_nndist, ENNReal.coe_ne_zero]) (edist_ne_top x y)
    (by rw [edist_nndist, edist_nndist, hr, ENNReal.coe_mul])

中文:
定理 ratio_unique_of_nndist_ne_zero
  结论: {α β F : 类型} [伪度量空间 α] [伪度量空间 β]
  证明: ratio_unique (by rwa [edist_nndist, ENNReal.coe_ne_zero]) (edist_ne_top x y)
    (by rw [edist_nndist, edist_nndist, hr, ENNReal.coe_mul])

Depends on / 依赖: ENNReal, ENNReal.coe_mul, ENNReal.coe_ne_zero, coe_mul, coe_ne_zero, edist_ne_top, edist_nndist, ratio_unique
-/
theorem ratio_unique_of_nndist_ne_zero {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [FunLike F α β] [DilationClass F α β] {f : F} {x y : α} {r : Real>=0} (hxy : nndist x y != 0)
    (hr : nndist (f x) (f y) = r * nndist x y) : r = ratio f :=
  ratio_unique (by rwa [edist_nndist, ENNReal.coe_ne_zero]) (edist_ne_top x y)
    (by rw [edist_nndist, edist_nndist, hr, ENNReal.coe_mul])

/--
theorem `ratio_unique_of_dist_ne_zero` / 定理 `ratio_unique_of_dist_ne_zero`

English:
theorem ratio_unique_of_dist_ne_zero
  statement: {α β} {F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
  proof: ratio_unique_of_nndist_ne_zero (NNReal.coe_ne_zero.1 hxy)
NNReal.eq by rw [coe_nndist, hr, NNReal.coe_mul, coe_nndist]

中文:
定理 ratio_unique_of_dist_ne_zero
  结论: {α β} {F : 类型} [伪度量空间 α] [伪度量空间 β]
  证明: ratio_unique_of_nndist_ne_zero (NNReal.coe_ne_zero.1 hxy)
NNReal.eq by rw [coe_nndist, hr, NNReal.coe_mul, coe_nndist]

Depends on / 依赖: NNReal, NNReal.coe_mul, NNReal.coe_ne_zero, NNReal.eq, coe_mul, coe_ne_zero, coe_nndist, ratio_unique_of_nndist_ne_zero
-/
theorem ratio_unique_of_dist_ne_zero {α β} {F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [FunLike F α β] [DilationClass F α β] {f : F} {x y : α} {r : Real>=0} (hxy : dist x y != 0)
    (hr : dist (f x) (f y) = r * dist x y) : r = ratio f :=
ratio_unique_of_nndist_ne_zero (NNReal.coe_ne_zero.1 hxy)
NNReal.eq by rw [coe_nndist, hr, NNReal.coe_mul, coe_nndist]

/--
Definition of `mkOfNNDistEq` / `mkOfNNDistEq` 的定义

English:
definition mkOfNNDistEq
  signature: {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α -> β)
  body: f
  edist_eq' := by
    rcases h with ⟨r, hne, h⟩
    refine ⟨r, hne, fun x y => ?_⟩
    rw [edist_nndist]; rw [edist_nndist]; rw [← ENNReal.coe_mul]; rw [h x y]

@[simp]

中文:
定义 mkOfNNDistEq
  签名: {α β} [伪度量空间 α] [伪度量空间 β] (f : α -> β)
  定义体: f
  edist_eq' := by
    rcases h with ⟨r, hne, h⟩
    refine ⟨r, hne, fun x y => ?_⟩
    rw [edist_nndist]; rw [edist_nndist]; rw [← ENNReal.coe_mul]; rw [h x y]

@[simp]
-/
def mkOfNNDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α -> β)
    (h : exists r : Real>=0, r != 0 ∧ forall x y : α, nndist (f x) (f y) = r * nndist x y) : α ->ᵈ β where
  toFun := f
  edist_eq' := by
    rcases h with ⟨r, hne, h⟩
    refine ⟨r, hne, fun x y => ?_⟩
    rw [edist_nndist]; rw [edist_nndist]; rw [← ENNReal.coe_mul]; rw [h x y]

@[simp]
/--
theorem `coe_mkOfNNDistEq` / 定理 `coe_mkOfNNDistEq`

English:
theorem coe_mkOfNNDistEq
  given: {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α -> β) (h)
  proof: rfl

@[simp]

中文:
定理 coe_mkOfNNDistEq
  条件: {α β} [伪度量空间 α] [伪度量空间 β] (f : α -> β) (h)
  证明: rfl

@[simp]
-/
theorem coe_mkOfNNDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α -> β) (h) :
    ⇑(mkOfNNDistEq f h : α ->ᵈ β) = f :=
  rfl

@[simp]
/--
theorem `mk_coe_of_nndist_eq` / 定理 `mk_coe_of_nndist_eq`

English:
theorem mk_coe_of_nndist_eq
  statement: {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α ->ᵈ β)
  proof: ext fun _ => rfl

中文:
定理 mk_coe_of_nndist_eq
  结论: {α β} [伪度量空间 α] [伪度量空间 β] (f : α ->ᵈ β)
  证明: ext fun _ => rfl
-/
theorem mk_coe_of_nndist_eq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α ->ᵈ β)
    (h) : Dilation.mkOfNNDistEq f h = f :=
  ext fun _ => rfl

/--
Definition of `mkOfDistEq` / `mkOfDistEq` 的定义

English:
definition mkOfDistEq
  signature: {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α -> β)
  body: mkOfNNDistEq f
    h.imp fun r hr =>
⟨hr.1, fun x y => NNReal.eq by rw [coe_nndist, hr.2, NNReal.coe_mul, coe_nndist]⟩

@[simp]

中文:
定义 mkOfDistEq
  签名: {α β} [伪度量空间 α] [伪度量空间 β] (f : α -> β)
  定义体: mkOfNNDistEq f
    h.imp fun r hr =>
⟨hr.1, fun x y => NNReal.eq by rw [coe_nndist, hr.2, NNReal.coe_mul, coe_nndist]⟩

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_mul, NNReal.eq, coe_mul, coe_nndist, h.imp, mkOfNNDistEq
-/
def mkOfDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α -> β)
    (h : exists r : Real>=0, r != 0 ∧ forall x y : α, dist (f x) (f y) = r * dist x y) : α ->ᵈ β :=
mkOfNNDistEq f
    h.imp fun r hr =>
⟨hr.1, fun x y => NNReal.eq by rw [coe_nndist, hr.2, NNReal.coe_mul, coe_nndist]⟩

@[simp]
/--
theorem `coe_mkOfDistEq` / 定理 `coe_mkOfDistEq`

English:
theorem coe_mkOfDistEq
  given: {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α -> β) (h)
  proof: rfl

@[simp]

中文:
定理 coe_mkOfDistEq
  条件: {α β} [伪度量空间 α] [伪度量空间 β] (f : α -> β) (h)
  证明: rfl

@[simp]
-/
theorem coe_mkOfDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α -> β) (h) :
    ⇑(mkOfDistEq f h : α ->ᵈ β) = f :=
  rfl

@[simp]
/--
theorem `mk_coe_of_dist_eq` / 定理 `mk_coe_of_dist_eq`

English:
theorem mk_coe_of_dist_eq
  given: {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α ->ᵈ β) (h)
  proof: ext fun _ => rfl

中文:
定理 mk_coe_of_dist_eq
  条件: {α β} [伪度量空间 α] [伪度量空间 β] (f : α ->ᵈ β) (h)
  证明: ext fun _ => rfl
-/
theorem mk_coe_of_dist_eq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α ->ᵈ β) (h) :
    Dilation.mkOfDistEq f h = f :=
  ext fun _ => rfl

end Setup

section PseudoEMetricDilation

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
variable [FunLike F α β] [DilationClass F α β]
variable (f : F)

/-- Every isometry is a dilation of ratio `1`. -/
@[simps]
/--
Definition of `_root_.Isometry.toDilation` / `_root_.Isometry.toDilation` 的定义

English:
definition _root_.Isometry.toDilation
  signature: (f : α -> β) (hf : Isometry f)
  body: f
  edist_eq' := ⟨1, one_ne_zero, by simpa using! hf⟩

@[simp]

中文:
定义 _root_.等距.toDilation
  签名: (f : α -> β) (hf : 等距 f)
  定义体: f
  edist_eq' := ⟨1, one_ne_zero, by simpa using! hf⟩

@[simp]
-/
def _root_.Isometry.toDilation (f : α -> β) (hf : Isometry f) : α ->ᵈ β where
  toFun := f
  edist_eq' := ⟨1, one_ne_zero, by simpa using! hf⟩

@[simp]
/--
lemma `_root_.Isometry.toDilation_ratio` / 引理 `_root_.Isometry.toDilation_ratio`

English:
lemma _root_.Isometry.toDilation_ratio
  given: {f : α -> β} {hf : Isometry f}
  statement: ratio hf.toDilation = 1
  proof: by
  by_cases! h : forall x y : α, edist x y = 0 ∨ edist x y = ⊤
  · exact ratio_of_trivial hf.toDilation h
  · obtain ⟨x, y, h₁, h₂⟩ := h
.symm exact ratio_unique h₁ h₂ (by simp [hf x y])

中文:
引理 _root_.等距.toDilation_ratio
  条件: {f : α -> β} {hf : 等距 f}
  结论: ratio hf.toDilation = 1
  证明: by
  by_cases! h : forall x y : α, edist x y = 0 ∨ edist x y = ⊤
  · exact ratio_of_trivial hf.toDilation h
  · obtain ⟨x, y, h₁, h₂⟩ := h
.symm exact ratio_unique h₁ h₂ (by simp [hf x y])

Depends on / 依赖: hf.toDilation, ratio_of_trivial, ratio_unique, toDilation
-/
lemma _root_.Isometry.toDilation_ratio {f : α -> β} {hf : Isometry f} : ratio hf.toDilation = 1 := by
  by_cases! h : forall x y : α, edist x y = 0 ∨ edist x y = ⊤
  · exact ratio_of_trivial hf.toDilation h
  · obtain ⟨x, y, h₁, h₂⟩ := h
.symm exact ratio_unique h₁ h₂ (by simp [hf x y])

/--
theorem `lipschitz` / 定理 `lipschitz`

English:
theorem lipschitz
  statement: LipschitzWith (ratio f) (f : α -> β)
  proof: fun x y => (edist_eq f x y).le

中文:
定理 lipschitz
  结论: LipschitzWith (ratio f) (f : α -> β)
  证明: fun x y => (edist_eq f x y).le

Depends on / 依赖: edist_eq
-/
theorem lipschitz : LipschitzWith (ratio f) (f : α -> β) := fun x y => (edist_eq f x y).le

/--
theorem `antilipschitz` / 定理 `antilipschitz`

English:
theorem antilipschitz
  statement: AntilipschitzWith (ratio f)⁻¹ (f : α -> β)
  proof: fun x y => by
  have hr : ratio f != 0 := ratio_ne_zero f
  exact mod_cast
    (ENNReal.mul_le_iff_le_inv (ENNReal.coe_ne_zero.2 hr) ENNReal.coe_ne_top).1 (edist_eq f x y).ge

中文:
定理 antilipschitz
  结论: AntilipschitzWith (ratio f)⁻¹ (f : α -> β)
  证明: fun x y => by
  have hr : ratio f != 0 := ratio_ne_zero f
  exact mod_cast
    (ENNReal.mul_le_iff_le_inv (ENNReal.coe_ne_zero.2 hr) ENNReal.coe_ne_top).1 (edist_eq f x y).ge

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, ENNReal.coe_ne_zero, ENNReal.mul_le_iff_le_inv, coe_ne_top, coe_ne_zero, edist_eq, mod_cast, mul_le_iff_le_inv, ratio_ne_zero
-/
theorem antilipschitz : AntilipschitzWith (ratio f)⁻¹ (f : α -> β) := fun x y => by
  have hr : ratio f != 0 := ratio_ne_zero f
  exact mod_cast
    (ENNReal.mul_le_iff_le_inv (ENNReal.coe_ne_zero.2 hr) ENNReal.coe_ne_top).1 (edist_eq f x y).ge

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  statement: {α : Type*} [EMetricSpace α] [FunLike F α β] [DilationClass F α β]
  proof: (antilipschitz f).injective

中文:
定理 injective
  结论: {α : 类型} [广义度量空间 α] [函数状 F α β] [Dilation类 F α β]
  证明: (antilipschitz f).injective
-/
protected theorem injective {α : Type*} [EMetricSpace α] [FunLike F α β] [DilationClass F α β]
    (f : F) :
    Injective f :=
  (antilipschitz f).injective

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (α) [PseudoEMetricSpace α]
  body: id
  edist_eq' := ⟨1, one_ne_zero, fun x y => by simp only [id, ENNReal.coe_one, one_mul]⟩

中文:
定义 id
  签名: (α) [PseudoEMetric空间 α]
  定义体: id
  edist_eq' := ⟨1, one_ne_zero, fun x y => by simp only [id, ENNReal.coe_one, one_mul]⟩
-/
protected def id (α) [PseudoEMetricSpace α] : α ->ᵈ α where
  toFun := id
  edist_eq' := ⟨1, one_ne_zero, fun x y => by simp only [id, ENNReal.coe_one, one_mul]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (α ->ᵈ α)
  body: ⟨Dilation.id α⟩

@[simp]

中文:
实例 :
  签名: 可居 (α ->ᵈ α)
  定义体: ⟨Dilation.id α⟩

@[simp]

Depends on / 依赖: Dilation, Dilation.id
-/
instance : Inhabited (α ->ᵈ α) :=
  ⟨Dilation.id α⟩

@[simp]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(Dilation.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(Dilation.id α) = id
  证明: rfl
-/
protected theorem coe_id : ⇑(Dilation.id α) = id :=
  rfl

/--
theorem `ratio_id` / 定理 `ratio_id`

English:
theorem ratio_id
  statement: ratio (Dilation.id α) = 1
  proof: by
  by_cases! h : forall x y : α, edist x y = 0 ∨ edist x y = ∞
  · rw [ratio, if_pos h]
  · rcases h with ⟨x, y, hne⟩
    refine (ratio_unique hne.1 hne.2 ?_).symm
    simp

中文:
定理 ratio_id
  结论: ratio (Dilation.id α) = 1
  证明: by
  by_cases! h : forall x y : α, edist x y = 0 ∨ edist x y = ∞
  · rw [ratio, if_pos h]
  · rcases h with ⟨x, y, hne⟩
    refine (ratio_unique hne.1 hne.2 ?_).symm
    simp

Depends on / 依赖: if_pos, ratio_unique
-/
theorem ratio_id : ratio (Dilation.id α) = 1 := by
  by_cases! h : forall x y : α, edist x y = 0 ∨ edist x y = ∞
  · rw [ratio, if_pos h]
  · rcases h with ⟨x, y, hne⟩
    refine (ratio_unique hne.1 hne.2 ?_).symm
    simp

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : β ->ᵈ γ) (f : α ->ᵈ β)
  body: g ∘ f
  edist_eq' := ⟨ratio g * ratio f, mul_ne_zero (ratio_ne_zero g) (ratio_ne_zero f),
    fun x y => by simp_rw [Function.comp, edist_eq, ENNReal.coe_mul, mul_assoc]⟩

中文:
定义 comp
  签名: (g : β ->ᵈ γ) (f : α ->ᵈ β)
  定义体: g ∘ f
  edist_eq' := ⟨ratio g * ratio f, mul_ne_zero (ratio_ne_zero g) (ratio_ne_zero f),
    fun x y => by simp_rw [Function.comp, edist_eq, ENNReal.coe_mul, mul_assoc]⟩
-/
def comp (g : β ->ᵈ γ) (f : α ->ᵈ β) : α ->ᵈ γ where
  toFun := g ∘ f
  edist_eq' := ⟨ratio g * ratio f, mul_ne_zero (ratio_ne_zero g) (ratio_ne_zero f),
    fun x y => by simp_rw [Function.comp, edist_eq, ENNReal.coe_mul, mul_assoc]⟩

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: {δ : Type*} [PseudoEMetricSpace δ] (f : α ->ᵈ β) (g : β ->ᵈ γ)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  结论: {δ : 类型} [PseudoEMetric空间 δ] (f : α ->ᵈ β) (g : β ->ᵈ γ)
  证明: rfl

@[simp]
-/
theorem comp_assoc {δ : Type*} [PseudoEMetricSpace δ] (f : α ->ᵈ β) (g : β ->ᵈ γ)
    (h : γ ->ᵈ δ) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (g : β ->ᵈ γ) (f : α ->ᵈ β)
  statement: (g.comp f : α -> γ) = g ∘ f
  proof: rfl

中文:
定理 coe_comp
  条件: (g : β ->ᵈ γ) (f : α ->ᵈ β)
  结论: (g.comp f : α -> γ) = g ∘ f
  证明: rfl
-/
theorem coe_comp (g : β ->ᵈ γ) (f : α ->ᵈ β) : (g.comp f : α -> γ) = g ∘ f :=
  rfl

/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g : β ->ᵈ γ) (f : α ->ᵈ β) (x : α)
  statement: (g.comp f : α -> γ) x = g (f x)
  proof: rfl

中文:
定理 comp_apply
  条件: (g : β ->ᵈ γ) (f : α ->ᵈ β) (x : α)
  结论: (g.comp f : α -> γ) x = g (f x)
  证明: rfl
-/
theorem comp_apply (g : β ->ᵈ γ) (f : α ->ᵈ β) (x : α) : (g.comp f : α -> γ) x = g (f x) :=
  rfl

/--
theorem `ratio_comp'` / 定理 `ratio_comp'`

English:
theorem ratio_comp'
  statement: {g : β ->ᵈ γ} {f : α ->ᵈ β}
  proof: by
  rcases hne with ⟨x, y, hα⟩
  have hgf := (edist_eq (g.comp f) x y).symm
  simp_rw [coe_comp, Function.comp, edist_eq, ← mul_assoc, ENNReal.mul_left_inj hα.1 hα.2]
    at hgf
  rwa [← ENNReal.coe_inj, ENNReal.coe_mul]

@[simp]

中文:
定理 ratio_comp'
  结论: {g : β ->ᵈ γ} {f : α ->ᵈ β}
  证明: by
  rcases hne with ⟨x, y, hα⟩
  have hgf := (edist_eq (g.comp f) x y).symm
  simp_rw [coe_comp, Function.comp, edist_eq, ← mul_assoc, ENNReal.mul_left_inj hα.1 hα.2]
    at hgf
  rwa [← ENNReal.coe_inj, ENNReal.coe_mul]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_inj, ENNReal.coe_mul, ENNReal.mul_left_inj, Function, Function.comp, coe_comp, coe_inj, coe_mul, edist_eq, g.comp, mul_assoc, mul_left_inj, simp_rw
-/
theorem ratio_comp' {g : β ->ᵈ γ} {f : α ->ᵈ β}
    (hne : exists x y : α, edist x y != 0 ∧ edist x y != ⊤) : ratio (g.comp f) = ratio g * ratio f := by
  rcases hne with ⟨x, y, hα⟩
  have hgf := (edist_eq (g.comp f) x y).symm
  simp_rw [coe_comp, Function.comp, edist_eq, ← mul_assoc, ENNReal.mul_left_inj hα.1 hα.2]
    at hgf
  rwa [← ENNReal.coe_inj, ENNReal.coe_mul]

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : α ->ᵈ β)
  statement: f.comp (Dilation.id α) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : α ->ᵈ β)
  结论: f.comp (Dilation.id α) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : α ->ᵈ β) : f.comp (Dilation.id α) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : α ->ᵈ β)
  statement: (Dilation.id β).comp f = f
  proof: ext fun _ => rfl

中文:
定理 id_comp
  条件: (f : α ->ᵈ β)
  结论: (Dilation.id β).comp f = f
  证明: ext fun _ => rfl
-/
theorem id_comp (f : α ->ᵈ β) : (Dilation.id β).comp f = f :=
  ext fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (α ->ᵈ α)
  body: Dilation.id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _

中文:
实例 :
  签名: 幺半群 (α ->ᵈ α)
  定义体: Dilation.id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _

Depends on / 依赖: Dilation, Dilation.id
-/
instance : Monoid (α ->ᵈ α) where
  one := Dilation.id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : α ->ᵈ α) = Dilation.id α
  proof: rfl

中文:
定理 one_def
  结论: (1 : α ->ᵈ α) = Dilation.id α
  证明: rfl
-/
theorem one_def : (1 : α ->ᵈ α) = Dilation.id α :=
  rfl

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (f g : α ->ᵈ α)
  statement: f * g = f.comp g
  proof: rfl

@[simp]

中文:
定理 mul_def
  条件: (f g : α ->ᵈ α)
  结论: f * g = f.comp g
  证明: rfl

@[simp]
-/
theorem mul_def (f g : α ->ᵈ α) : f * g = f.comp g :=
  rfl

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : α ->ᵈ α) = id
  proof: rfl

@[simp]

中文:
定理 coe_one
  结论: ⇑(1 : α ->ᵈ α) = id
  证明: rfl

@[simp]
-/
theorem coe_one : ⇑(1 : α ->ᵈ α) = id :=
  rfl

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (f g : α ->ᵈ α)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

中文:
定理 coe_mul
  条件: (f g : α ->ᵈ α)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl
-/
theorem coe_mul (f g : α ->ᵈ α) : ⇑(f * g) = f ∘ g :=
  rfl

/--
theorem `ratio_one` / 定理 `ratio_one`

English:
theorem ratio_one
  statement: ratio (1 : α ->ᵈ α) = 1
  proof: ratio_id

@[simp]

中文:
定理 ratio_one
  结论: ratio (1 : α ->ᵈ α) = 1
  证明: ratio_id

@[simp]
-/
@[simp] theorem ratio_one : ratio (1 : α ->ᵈ α) = 1 := ratio_id

@[simp]
/--
theorem `ratio_mul` / 定理 `ratio_mul`

English:
theorem ratio_mul
  given: (f g : α ->ᵈ α)
  statement: ratio (f * g) = ratio f * ratio g
  proof: by
  by_cases! h : forall x y : α, edist x y = 0 ∨ edist x y = ∞
  · simp [ratio_of_trivial, h]
  exact ratio_comp' h

中文:
定理 ratio_mul
  条件: (f g : α ->ᵈ α)
  结论: ratio (f * g) = ratio f * ratio g
  证明: by
  by_cases! h : forall x y : α, edist x y = 0 ∨ edist x y = ∞
  · simp [ratio_of_trivial, h]
  exact ratio_comp' h

Depends on / 依赖: ratio_comp, ratio_of_trivial
-/
theorem ratio_mul (f g : α ->ᵈ α) : ratio (f * g) = ratio f * ratio g := by
  by_cases! h : forall x y : α, edist x y = 0 ∨ edist x y = ∞
  · simp [ratio_of_trivial, h]
  exact ratio_comp' h

/-- `Dilation.ratio` as a monoid homomorphism from `α →ᵈ α` to `ℝ≥0`. -/
@[simps]
/--
Definition of `ratioHom` / `ratioHom` 的定义

English:
definition ratioHom
  signature: : (α ->ᵈ α) ->* Real>=0
  body: ⟨⟨ratio, ratio_one⟩, ratio_mul⟩

@[simp]

中文:
定义 ratioHom
  签名: : (α ->ᵈ α) ->* 实数>=0
  定义体: ⟨⟨ratio, ratio_one⟩, ratio_mul⟩

@[simp]

Depends on / 依赖: ratio_mul, ratio_one
-/
def ratioHom : (α ->ᵈ α) ->* Real>=0 := ⟨⟨ratio, ratio_one⟩, ratio_mul⟩

@[simp]
/--
theorem `ratio_pow` / 定理 `ratio_pow`

English:
theorem ratio_pow
  given: (f : α ->ᵈ α) (n : Nat)
  statement: ratio (f ^ n) = ratio f ^ n
  proof: ratioHom.map_pow _ _

@[simp]

中文:
定理 ratio_pow
  条件: (f : α ->ᵈ α) (n : 自然数)
  结论: ratio (f ^ n) = ratio f ^ n
  证明: ratioHom.map_pow _ _

@[simp]

Depends on / 依赖: map_pow, ratioHom, ratioHom.map_pow
-/
theorem ratio_pow (f : α ->ᵈ α) (n : Nat) : ratio (f ^ n) = ratio f ^ n :=
  ratioHom.map_pow _ _

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : β ->ᵈ γ} {f : α ->ᵈ β} (hf : Surjective f)
  proof: ⟨fun h => Dilation.ext hf.forall.2 (Dilation.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]

中文:
定理 cancel_right
  条件: {g₁ g₂ : β ->ᵈ γ} {f : α ->ᵈ β} (hf : 满射 f)
  证明: ⟨fun h => Dilation.ext hf.forall.2 (Dilation.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]

Depends on / 依赖: Dilation, Dilation.ext, Dilation.ext_iff, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : β ->ᵈ γ} {f : α ->ᵈ β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => Dilation.ext hf.forall.2 (Dilation.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : β ->ᵈ γ} {f₁ f₂ : α ->ᵈ β} (hg : Injective g)
  proof: ⟨fun h => Dilation.ext fun x => hg by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

中文:
定理 cancel_left
  条件: {g : β ->ᵈ γ} {f₁ f₂ : α ->ᵈ β} (hg : 单射 g)
  证明: ⟨fun h => Dilation.ext fun x => hg by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

Depends on / 依赖: Dilation, Dilation.ext, comp_apply
-/
theorem cancel_left {g : β ->ᵈ γ} {f₁ f₂ : α ->ᵈ β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => Dilation.ext fun x => hg by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

/--
theorem `isUniformInducing` / 定理 `isUniformInducing`

English:
theorem isUniformInducing
  statement: IsUniformInducing (f : α -> β)
  proof: (antilipschitz f).isUniformInducing (lipschitz f).uniformContinuous

中文:
定理 isUniformInducing
  结论: 是UniformInducing (f : α -> β)
  证明: (antilipschitz f).isUniformInducing (lipschitz f).uniformContinuous

Depends on / 依赖: antilipschitz, isUniformInducing, lipschitz, uniformContinuous
-/
theorem isUniformInducing : IsUniformInducing (f : α -> β) :=
  (antilipschitz f).isUniformInducing (lipschitz f).uniformContinuous

/--
theorem `tendsto_nhds_iff` / 定理 `tendsto_nhds_iff`

English:
theorem tendsto_nhds_iff
  given: {ι : Type*} {g : ι -> α} {a : Filter ι} {b : α}
  proof: (Dilation.isUniformInducing f).isInducing.tendsto_nhds_iff

中文:
定理 tendsto_nhds_iff
  条件: {ι : 类型} {g : ι -> α} {a : 滤子 ι} {b : α}
  证明: (Dilation.isUniformInducing f).isInducing.tendsto_nhds_iff

Depends on / 依赖: Dilation, Dilation.isUniformInducing, isInducing, isInducing.tendsto_nhds_iff, isUniformInducing, tendsto_nhds_iff
-/
theorem tendsto_nhds_iff {ι : Type*} {g : ι -> α} {a : Filter ι} {b : α} :
    Filter.Tendsto g a (𝓝 b) ↔ Filter.Tendsto ((f : α -> β) ∘ g) a (𝓝 (f b)) :=
  (Dilation.isUniformInducing f).isInducing.tendsto_nhds_iff

/--
theorem `toContinuous` / 定理 `toContinuous`

English:
theorem toContinuous
  statement: Continuous (f : α -> β)
  proof: (lipschitz f).continuous

中文:
定理 toContinuous
  结论: 连续 (f : α -> β)
  证明: (lipschitz f).continuous

Depends on / 依赖: continuous, lipschitz
-/
theorem toContinuous : Continuous (f : α -> β) :=
  (lipschitz f).continuous

/--
theorem `ediam_image` / 定理 `ediam_image`

English:
theorem ediam_image
  given: (s : Set α)
  statement: ediam ((f : α -> β) '' s) = ratio f * ediam s
  proof: by
  refine ((lipschitz f).ediam_image_le s).antisymm ?_
  apply ENNReal.mul_le_of_le_div'
  rw [div_eq_mul_inv]; rw [mul_comm]; rw [← ENNReal.coe_inv]
  exacts [(antilipschitz f).le_mul_ediam_image s, ratio_ne_zero f]

中文:
定理 ediam_image
  条件: (s : 集合 α)
  结论: ediam ((f : α -> β) '' s) = ratio f * ediam s
  证明: by
  refine ((lipschitz f).ediam_image_le s).antisymm ?_
  apply ENNReal.mul_le_of_le_div'
  rw [div_eq_mul_inv]; rw [mul_comm]; rw [← ENNReal.coe_inv]
  exacts [(antilipschitz f).le_mul_ediam_image s, ratio_ne_zero f]

Depends on / 依赖: ENNReal, ENNReal.coe_inv, ENNReal.mul_le_of_le_div, antilipschitz, antisymm, coe_inv, div_eq_mul_inv, ediam_image_le, exacts, le_mul_ediam_image, lipschitz, mul_comm, mul_le_of_le_div, ratio_ne_zero
-/
theorem ediam_image (s : Set α) : ediam ((f : α -> β) '' s) = ratio f * ediam s := by
  refine ((lipschitz f).ediam_image_le s).antisymm ?_
  apply ENNReal.mul_le_of_le_div'
  rw [div_eq_mul_inv]; rw [mul_comm]; rw [← ENNReal.coe_inv]
  exacts [(antilipschitz f).le_mul_ediam_image s, ratio_ne_zero f]

/--
theorem `ediam_range` / 定理 `ediam_range`

English:
theorem ediam_range
  statement: ediam (range (f : α -> β)) = ratio f * ediam (univ : Set α)
  proof: by
  rw [← image_univ]; exact ediam_image f univ

中文:
定理 ediam_range
  结论: ediam (range (f : α -> β)) = ratio f * ediam (univ : 集合 α)
  证明: by
  rw [← image_univ]; exact ediam_image f univ

Depends on / 依赖: ediam_image, image_univ
-/
theorem ediam_range : ediam (range (f : α -> β)) = ratio f * ediam (univ : Set α) := by
  rw [← image_univ]; exact ediam_image f univ

/--
theorem `mapsTo_eball` / 定理 `mapsTo_eball`

English:
theorem mapsTo_eball
  given: (x : α) (r : Real>=0∞)
  proof: fun y (hy : _ < r) => by rw [Metric.mem_eball, edist_eq f y x]; gcongr <;> simp [ratio_ne_zero, *]

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_ball := mapsTo_eball

中文:
定理 mapsTo_eball
  条件: (x : α) (r : 实数>=0∞)
  证明: fun y (hy : _ < r) => by rw [Metric.mem_eball, edist_eq f y x]; gcongr <;> simp [ratio_ne_zero, *]

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_ball := mapsTo_eball

Depends on / 依赖: Metric, Metric.mem_eball, edist_eq, mem_eball, ratio_ne_zero
-/
theorem mapsTo_eball (x : α) (r : Real>=0∞) :
    MapsTo (f : α -> β) (Metric.eball x r) (Metric.eball (f x) (ratio f * r)) :=
  fun y (hy : _ < r) => by rw [Metric.mem_eball, edist_eq f y x]; gcongr <;> simp [ratio_ne_zero, *]

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_ball := mapsTo_eball

/--
theorem `mapsTo_closedEBall` / 定理 `mapsTo_closedEBall`

English:
theorem mapsTo_closedEBall
  given: (x : α) (r' : Real>=0∞)
  proof: fun y hy => (edist_eq f y x).trans_le by gcongr; exact hy

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_closedBall := mapsTo_closedEBall

中文:
定理 mapsTo_closedEBall
  条件: (x : α) (r' : 实数>=0∞)
  证明: fun y hy => (edist_eq f y x).trans_le by gcongr; exact hy

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_closedBall := mapsTo_closedEBall

Depends on / 依赖: edist_eq, trans_le
-/
theorem mapsTo_closedEBall (x : α) (r' : Real>=0∞) :
    MapsTo (f : α -> β) (Metric.closedEBall x r') (Metric.closedEBall (f x) (ratio f * r')) :=
fun y hy => (edist_eq f y x).trans_le by gcongr; exact hy

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_closedBall := mapsTo_closedEBall

/--
theorem `comp_continuousOn_iff` / 定理 `comp_continuousOn_iff`

English:
theorem comp_continuousOn_iff
  given: {γ} [TopologicalSpace γ] {g : γ -> α} {s : Set γ}
  proof: (Dilation.isUniformInducing f).isInducing.continuousOn_iff.symm

中文:
定理 comp_continuousOn_iff
  条件: {γ} [拓扑空间 γ] {g : γ -> α} {s : 集合 γ}
  证明: (Dilation.isUniformInducing f).isInducing.continuousOn_iff.symm

Depends on / 依赖: Dilation, Dilation.isUniformInducing, continuousOn_iff, isInducing, isInducing.continuousOn_iff.symm, isUniformInducing
-/
theorem comp_continuousOn_iff {γ} [TopologicalSpace γ] {g : γ -> α} {s : Set γ} :
    ContinuousOn ((f : α -> β) ∘ g) s ↔ ContinuousOn g s :=
  (Dilation.isUniformInducing f).isInducing.continuousOn_iff.symm

/--
theorem `comp_continuous_iff` / 定理 `comp_continuous_iff`

English:
theorem comp_continuous_iff
  given: {γ} [TopologicalSpace γ] {g : γ -> α}
  proof: (Dilation.isUniformInducing f).isInducing.continuous_iff.symm

中文:
定理 comp_continuous_iff
  条件: {γ} [拓扑空间 γ] {g : γ -> α}
  证明: (Dilation.isUniformInducing f).isInducing.continuous_iff.symm

Depends on / 依赖: Dilation, Dilation.isUniformInducing, continuous_iff, isInducing, isInducing.continuous_iff.symm, isUniformInducing
-/
theorem comp_continuous_iff {γ} [TopologicalSpace γ] {g : γ -> α} :
    Continuous ((f : α -> β) ∘ g) ↔ Continuous g :=
  (Dilation.isUniformInducing f).isInducing.continuous_iff.symm

end PseudoEMetricDilation

section EMetricDilation

variable [EMetricSpace α]
variable [FunLike F α β]

/--
lemma `isUniformEmbedding` / 引理 `isUniformEmbedding`

English:
lemma isUniformEmbedding
  given: [PseudoEMetricSpace β] [DilationClass F α β] (f : F)
  proof: (antilipschitz f).isUniformEmbedding (lipschitz f).uniformContinuous

中文:
引理 isUniformEmbedding
  条件: [PseudoEMetric空间 β] [Dilation类 F α β] (f : F)
  证明: (antilipschitz f).isUniformEmbedding (lipschitz f).uniformContinuous

Depends on / 依赖: antilipschitz, isUniformEmbedding, lipschitz, uniformContinuous
-/
lemma isUniformEmbedding [PseudoEMetricSpace β] [DilationClass F α β] (f : F) :
    IsUniformEmbedding f :=
  (antilipschitz f).isUniformEmbedding (lipschitz f).uniformContinuous

/--
theorem `isEmbedding` / 定理 `isEmbedding`

English:
theorem isEmbedding
  given: [PseudoEMetricSpace β] [DilationClass F α β] (f : F)
  proof: (Dilation.isUniformEmbedding f).isEmbedding

中文:
定理 isEmbedding
  条件: [PseudoEMetric空间 β] [Dilation类 F α β] (f : F)
  证明: (Dilation.isUniformEmbedding f).isEmbedding

Depends on / 依赖: Dilation, Dilation.isUniformEmbedding, isEmbedding, isUniformEmbedding
-/
theorem isEmbedding [PseudoEMetricSpace β] [DilationClass F α β] (f : F) :
    IsEmbedding (f : α -> β) :=
  (Dilation.isUniformEmbedding f).isEmbedding

/--
lemma `isClosedEmbedding` / 引理 `isClosedEmbedding`

English:
lemma isClosedEmbedding
  given: [CompleteSpace α] [EMetricSpace β] [DilationClass F α β] (f : F)
  proof: (antilipschitz f).isClosedEmbedding (lipschitz f).uniformContinuous

中文:
引理 isClosedEmbedding
  条件: [完备空间 α] [广义度量空间 β] [Dilation类 F α β] (f : F)
  证明: (antilipschitz f).isClosedEmbedding (lipschitz f).uniformContinuous

Depends on / 依赖: antilipschitz, isClosedEmbedding, lipschitz, uniformContinuous
-/
lemma isClosedEmbedding [CompleteSpace α] [EMetricSpace β] [DilationClass F α β] (f : F) :
    IsClosedEmbedding f :=
  (antilipschitz f).isClosedEmbedding (lipschitz f).uniformContinuous

end EMetricDilation

/-- Ratio of the composition `g.comp f` of two dilations is the product of their ratios. We assume
that the domain `α` of `f` is a nontrivial metric space, otherwise
`Dilation.ratio f = Dilation.ratio (g.comp f) = 1` but `Dilation.ratio g` may have any value.

See also `Dilation.ratio_comp'` for a version that works for more general spaces. -/
@[simp]
/--
theorem `ratio_comp` / 定理 `ratio_comp`

English:
theorem ratio_comp
  statement: [MetricSpace α] [Nontrivial α] [PseudoEMetricSpace β]
  proof: ratio_comp'
    let ⟨x, y, hne⟩ := exists_pair_ne α; ⟨x, y, mt edist_eq_zero.1 hne, edist_ne_top _ _⟩

中文:
定理 ratio_comp
  结论: [度量空间 α] [非平凡 α] [PseudoEMetric空间 β]
  证明: ratio_comp'
    let ⟨x, y, hne⟩ := exists_pair_ne α; ⟨x, y, mt edist_eq_zero.1 hne, edist_ne_top _ _⟩

Depends on / 依赖: edist_eq_zero, edist_ne_top, exists_pair_ne, ratio_comp
-/
theorem ratio_comp [MetricSpace α] [Nontrivial α] [PseudoEMetricSpace β]
    [PseudoEMetricSpace γ] {g : β ->ᵈ γ} {f : α ->ᵈ β} : ratio (g.comp f) = ratio g * ratio f :=
ratio_comp'
    let ⟨x, y, hne⟩ := exists_pair_ne α; ⟨x, y, mt edist_eq_zero.1 hne, edist_ne_top _ _⟩

section PseudoMetricDilation

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β] [DilationClass F α β] (f : F)

/--
theorem `diam_image` / 定理 `diam_image`

English:
theorem diam_image
  given: (s : Set α)
  statement: diam ((f : α -> β) '' s) = ratio f * diam s
  proof: by
  simp [diam, ediam_image, ENNReal.toReal_mul]

中文:
定理 diam_image
  条件: (s : 集合 α)
  结论: diam ((f : α -> β) '' s) = ratio f * diam s
  证明: by
  simp [diam, ediam_image, ENNReal.toReal_mul]

Depends on / 依赖: ENNReal, ENNReal.toReal_mul, ediam_image, toReal_mul
-/
theorem diam_image (s : Set α) : diam ((f : α -> β) '' s) = ratio f * diam s := by
  simp [diam, ediam_image, ENNReal.toReal_mul]

/--
theorem `diam_range` / 定理 `diam_range`

English:
theorem diam_range
  statement: diam (range (f : α -> β)) = ratio f * diam (univ : Set α)
  proof: by
  rw [← image_univ]; rw [diam_image]

中文:
定理 diam_range
  结论: diam (range (f : α -> β)) = ratio f * diam (univ : 集合 α)
  证明: by
  rw [← image_univ]; rw [diam_image]

Depends on / 依赖: diam_image, image_univ
-/
theorem diam_range : diam (range (f : α -> β)) = ratio f * diam (univ : Set α) := by
  rw [← image_univ]; rw [diam_image]

/--
theorem `mapsTo_ball` / 定理 `mapsTo_ball`

English:
theorem mapsTo_ball
  given: (x : α) (r' : Real)
  proof: fun y hy => (dist_eq f y x).trans_lt by gcongr; exacts [ratio_pos _, hy]

中文:
定理 mapsTo_ball
  条件: (x : α) (r' : 实数)
  证明: fun y hy => (dist_eq f y x).trans_lt by gcongr; exacts [ratio_pos _, hy]

Depends on / 依赖: dist_eq, exacts, ratio_pos, trans_lt
-/
theorem mapsTo_ball (x : α) (r' : Real) :
    MapsTo (f : α -> β) (Metric.ball x r') (Metric.ball (f x) (ratio f * r')) :=
fun y hy => (dist_eq f y x).trans_lt by gcongr; exacts [ratio_pos _, hy]

/--
theorem `mapsTo_sphere` / 定理 `mapsTo_sphere`

English:
theorem mapsTo_sphere
  given: (x : α) (r' : Real)
  proof: fun y hy => Metric.mem_sphere.mp hy ▸ dist_eq f y x

中文:
定理 mapsTo_sphere
  条件: (x : α) (r' : 实数)
  证明: fun y hy => Metric.mem_sphere.mp hy ▸ dist_eq f y x

Depends on / 依赖: Metric, Metric.mem_sphere.mp, dist_eq, mem_sphere
-/
theorem mapsTo_sphere (x : α) (r' : Real) :
    MapsTo (f : α -> β) (Metric.sphere x r') (Metric.sphere (f x) (ratio f * r')) :=
  fun y hy => Metric.mem_sphere.mp hy ▸ dist_eq f y x

/--
theorem `mapsTo_closedBall` / 定理 `mapsTo_closedBall`

English:
theorem mapsTo_closedBall
  given: (x : α) (r' : Real)
  proof: fun y hy => (dist_eq f y x).trans_le mul_le_mul_of_nonneg_left hy (NNReal.coe_nonneg _)

中文:
定理 mapsTo_closedBall
  条件: (x : α) (r' : 实数)
  证明: fun y hy => (dist_eq f y x).trans_le mul_le_mul_of_nonneg_left hy (NNReal.coe_nonneg _)

Depends on / 依赖: NNReal, NNReal.coe_nonneg, coe_nonneg, dist_eq, mul_le_mul_of_nonneg_left, trans_le
-/
theorem mapsTo_closedBall (x : α) (r' : Real) :
    MapsTo (f : α -> β) (Metric.closedBall x r') (Metric.closedBall (f x) (ratio f * r')) :=
fun y hy => (dist_eq f y x).trans_le mul_le_mul_of_nonneg_left hy (NNReal.coe_nonneg _)

/--
lemma `tendsto_cobounded` / 引理 `tendsto_cobounded`

English:
lemma tendsto_cobounded
  statement: Filter.Tendsto f (cobounded α) (cobounded β)
  proof: (Dilation.antilipschitz f).tendsto_cobounded

@[simp]

中文:
引理 tendsto_cobounded
  结论: 滤子.收敛 f (cobounded α) (cobounded β)
  证明: (Dilation.antilipschitz f).tendsto_cobounded

@[simp]

Depends on / 依赖: Dilation, Dilation.antilipschitz, antilipschitz, tendsto_cobounded
-/
lemma tendsto_cobounded : Filter.Tendsto f (cobounded α) (cobounded β) :=
  (Dilation.antilipschitz f).tendsto_cobounded

@[simp]
/--
lemma `comap_cobounded` / 引理 `comap_cobounded`

English:
lemma comap_cobounded
  statement: Filter.comap f (cobounded β) = cobounded α
  proof: le_antisymm (lipschitz f).comap_cobounded_le (tendsto_cobounded f).le_comap

中文:
引理 comap_cobounded
  结论: 滤子.comap f (cobounded β) = cobounded α
  证明: le_antisymm (lipschitz f).comap_cobounded_le (tendsto_cobounded f).le_comap

Depends on / 依赖: comap_cobounded_le, le_antisymm, le_comap, lipschitz, tendsto_cobounded
-/
lemma comap_cobounded : Filter.comap f (cobounded β) = cobounded α :=
  le_antisymm (lipschitz f).comap_cobounded_le (tendsto_cobounded f).le_comap

end PseudoMetricDilation

end Dilation
