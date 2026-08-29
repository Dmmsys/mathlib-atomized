/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Topology.Algebra.Group.Torsor
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Torsors of additive normed group actions.

This file defines torsors of additive normed group actions, with a
metric space structure. The motivating case is Euclidean affine
spaces.
-/

@[expose] public section


noncomputable section

open NNReal Topology

open Filter

/--
Definition of `NormedAddTorsor` / `NormedAddTorsor` 的定义

English:
class NormedAddTorsor
  parameters: (V : outParam Type*) (P : Type*) [SeminormedAddCommGroup V]
  extends: AddTorsor V P
  axioms and operations (1):
    - dist_eq_norm' : forall x y : P, dist x y = ‖(x -ᵥ y : V)‖

中文:
类 NormedAddTorsor
  参数: (V : outParam 类型) (P : 类型) [SeminormedAddComm群 V]
  继承: 加法Torsor V P
  公理与运算 (1 个):
    - dist_eq_norm' : 对任意 x y : P, dist x y = ‖(x -ᵥ y : V)‖
-/
class NormedAddTorsor (V : outParam Type*) (P : Type*) [SeminormedAddCommGroup V]
  [PseudoMetricSpace P] extends AddTorsor V P where
  dist_eq_norm' : forall x y : P, dist x y = ‖(x -ᵥ y : V)‖

/-- Shortcut instance to help typeclass inference out. -/
instance (priority := 100) NormedAddTorsor.toAddTorsor' {V P : Type*} [NormedAddCommGroup V]
    [MetricSpace P] [NormedAddTorsor V P] : AddTorsor V P :=
  NormedAddTorsor.toAddTorsor

variable {α V P W Q : Type*} [SeminormedAddCommGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]
  [SeminormedAddCommGroup W] [PseudoMetricSpace Q] [NormedAddTorsor W Q]

instance (priority := 100) NormedAddTorsor.to_isIsIsometricVAdd : IsIsometricVAdd V P :=
  ⟨fun c => Isometry.of_dist_eq fun x y => by
    simp [NormedAddTorsor.dist_eq_norm']⟩

/-- A `SeminormedAddCommGroup` is a `NormedAddTorsor` over itself. -/
instance (priority := 100) SeminormedAddCommGroup.toNormedAddTorsor : NormedAddTorsor V V where
  dist_eq_norm' := dist_eq_norm

-- Because of the AddTorsor.nonempty instance.
/--
Instance `AffineSubspace.toNormedAddTorsor` / 实例 `AffineSubspace.toNormedAddTorsor`

English:
instance AffineSubspace.toNormedAddTorsor
  signature: {R : Type*} [Ring R] [Module R V]
  body: { AffineSubspace.toAddTorsor s with
    dist_eq_norm' := fun x y => NormedAddTorsor.dist_eq_norm' x.val y.val }

中文:
实例 仿射子空间.toNormedAddTorsor
  签名: {R : 类型} [环 R] [模 R V]
  定义体: { AffineSubspace.toAddTorsor s with
    dist_eq_norm' := fun x y => NormedAddTorsor.dist_eq_norm' x.val y.val }

Depends on / 依赖: AffineSubspace, AffineSubspace.toAddTorsor, NormedAddTorsor, NormedAddTorsor.dist_eq_norm, dist_eq_norm, toAddTorsor, x.val, y.val
-/
instance AffineSubspace.toNormedAddTorsor {R : Type*} [Ring R] [Module R V]
    (s : AffineSubspace R P) [Nonempty s] : NormedAddTorsor s.direction s :=
  { AffineSubspace.toAddTorsor s with
    dist_eq_norm' := fun x y => NormedAddTorsor.dist_eq_norm' x.val y.val }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedAddTorsor (V × W) (P × Q)
  body: by
    simp only [Prod.dist_eq, NormedAddTorsor.dist_eq_norm', Prod.norm_def, Prod.fst_vsub,
      Prod.snd_vsub]

中文:
实例 :
  签名: NormedAddTorsor (V × W) (P × Q)
  定义体: by
    simp only [Prod.dist_eq, NormedAddTorsor.dist_eq_norm', Prod.norm_def, Prod.fst_vsub,
      Prod.snd_vsub]

Depends on / 依赖: NormedAddTorsor, NormedAddTorsor.dist_eq_norm, Prod.dist_eq, Prod.fst_vsub, Prod.norm_def, Prod.snd_vsub, dist_eq, dist_eq_norm, fst_vsub, norm_def, snd_vsub
-/
instance : NormedAddTorsor (V × W) (P × Q) where
  dist_eq_norm' x y := by
    simp only [Prod.dist_eq, NormedAddTorsor.dist_eq_norm', Prod.norm_def, Prod.fst_vsub,
      Prod.snd_vsub]

section

variable (V W)

/--
theorem `dist_eq_norm_vsub` / 定理 `dist_eq_norm_vsub`

English:
theorem dist_eq_norm_vsub
  given: (x y : P)
  statement: dist x y = ‖x -ᵥ y‖
  proof: NormedAddTorsor.dist_eq_norm' x y

中文:
定理 dist_eq_norm_vsub
  条件: (x y : P)
  结论: dist x y = ‖x -ᵥ y‖
  证明: NormedAddTorsor.dist_eq_norm' x y

Depends on / 依赖: NormedAddTorsor, NormedAddTorsor.dist_eq_norm, dist_eq_norm
-/
theorem dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖ :=
  NormedAddTorsor.dist_eq_norm' x y

/--
theorem `nndist_eq_nnnorm_vsub` / 定理 `nndist_eq_nnnorm_vsub`

English:
theorem nndist_eq_nnnorm_vsub
  given: (x y : P)
  statement: nndist x y = ‖x -ᵥ y‖₊
  proof: NNReal.eq dist_eq_norm_vsub V x y

中文:
定理 nndist_eq_nnnorm_vsub
  条件: (x y : P)
  结论: nndist x y = ‖x -ᵥ y‖₊
  证明: NNReal.eq dist_eq_norm_vsub V x y

Depends on / 依赖: NNReal, NNReal.eq, dist_eq_norm_vsub
-/
theorem nndist_eq_nnnorm_vsub (x y : P) : nndist x y = ‖x -ᵥ y‖₊ :=
NNReal.eq dist_eq_norm_vsub V x y


/--
theorem `dist_eq_norm_vsub'` / 定理 `dist_eq_norm_vsub'`

English:
theorem dist_eq_norm_vsub'
  given: (x y : P)
  statement: dist x y = ‖y -ᵥ x‖
  proof: (dist_comm _ _).trans (dist_eq_norm_vsub _ _ _)

中文:
定理 dist_eq_norm_vsub'
  条件: (x y : P)
  结论: dist x y = ‖y -ᵥ x‖
  证明: (dist_comm _ _).trans (dist_eq_norm_vsub _ _ _)

Depends on / 依赖: dist_comm, dist_eq_norm_vsub
-/
theorem dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖ :=
  (dist_comm _ _).trans (dist_eq_norm_vsub _ _ _)

/--
theorem `nndist_eq_nnnorm_vsub'` / 定理 `nndist_eq_nnnorm_vsub'`

English:
theorem nndist_eq_nnnorm_vsub'
  given: (x y : P)
  statement: nndist x y = ‖y -ᵥ x‖₊
  proof: NNReal.eq dist_eq_norm_vsub' V x y

中文:
定理 nndist_eq_nnnorm_vsub'
  条件: (x y : P)
  结论: nndist x y = ‖y -ᵥ x‖₊
  证明: NNReal.eq dist_eq_norm_vsub' V x y

Depends on / 依赖: NNReal, NNReal.eq, dist_eq_norm_vsub
-/
theorem nndist_eq_nnnorm_vsub' (x y : P) : nndist x y = ‖y -ᵥ x‖₊ :=
NNReal.eq dist_eq_norm_vsub' V x y

end

/--
theorem `dist_vadd_cancel_left` / 定理 `dist_vadd_cancel_left`

English:
theorem dist_vadd_cancel_left
  given: (v : V) (x y : P)
  statement: dist (v +ᵥ x) (v +ᵥ y) = dist x y
  proof: dist_vadd _ _ _

中文:
定理 dist_vadd_cancel_left
  条件: (v : V) (x y : P)
  结论: dist (v +ᵥ x) (v +ᵥ y) = dist x y
  证明: dist_vadd _ _ _

Depends on / 依赖: dist_vadd
-/
theorem dist_vadd_cancel_left (v : V) (x y : P) : dist (v +ᵥ x) (v +ᵥ y) = dist x y :=
  dist_vadd _ _ _

/--
theorem `nndist_vadd_cancel_left` / 定理 `nndist_vadd_cancel_left`

English:
theorem nndist_vadd_cancel_left
  given: (v : V) (x y : P)
  statement: nndist (v +ᵥ x) (v +ᵥ y) = nndist x y
  proof: NNReal.eq dist_vadd_cancel_left _ _ _

@[simp]

中文:
定理 nndist_vadd_cancel_left
  条件: (v : V) (x y : P)
  结论: nndist (v +ᵥ x) (v +ᵥ y) = nndist x y
  证明: NNReal.eq dist_vadd_cancel_left _ _ _

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, dist_vadd_cancel_left
-/
theorem nndist_vadd_cancel_left (v : V) (x y : P) : nndist (v +ᵥ x) (v +ᵥ y) = nndist x y :=
NNReal.eq dist_vadd_cancel_left _ _ _

@[simp]
/--
theorem `dist_vadd_cancel_right` / 定理 `dist_vadd_cancel_right`

English:
theorem dist_vadd_cancel_right
  given: (v₁ v₂ : V) (x : P)
  statement: dist (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂
  proof: by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm]; rw [vadd_vsub_vadd_cancel_right]

@[simp]

中文:
定理 dist_vadd_cancel_right
  条件: (v₁ v₂ : V) (x : P)
  结论: dist (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂
  证明: by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm]; rw [vadd_vsub_vadd_cancel_right]

@[simp]

Depends on / 依赖: dist_eq_norm, dist_eq_norm_vsub, vadd_vsub_vadd_cancel_right
-/
theorem dist_vadd_cancel_right (v₁ v₂ : V) (x : P) : dist (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂ := by
  rw [dist_eq_norm_vsub V]; rw [dist_eq_norm]; rw [vadd_vsub_vadd_cancel_right]

@[simp]
/--
theorem `nndist_vadd_cancel_right` / 定理 `nndist_vadd_cancel_right`

English:
theorem nndist_vadd_cancel_right
  given: (v₁ v₂ : V) (x : P)
  statement: nndist (v₁ +ᵥ x) (v₂ +ᵥ x) = nndist v₁ v₂
  proof: NNReal.eq dist_vadd_cancel_right _ _ _

@[simp]

中文:
定理 nndist_vadd_cancel_right
  条件: (v₁ v₂ : V) (x : P)
  结论: nndist (v₁ +ᵥ x) (v₂ +ᵥ x) = nndist v₁ v₂
  证明: NNReal.eq dist_vadd_cancel_right _ _ _

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, dist_vadd_cancel_right
-/
theorem nndist_vadd_cancel_right (v₁ v₂ : V) (x : P) : nndist (v₁ +ᵥ x) (v₂ +ᵥ x) = nndist v₁ v₂ :=
NNReal.eq dist_vadd_cancel_right _ _ _

@[simp]
/--
theorem `dist_vadd_left` / 定理 `dist_vadd_left`

English:
theorem dist_vadd_left
  given: (v : V) (x : P)
  statement: dist (v +ᵥ x) x = ‖v‖
  proof: by
  simp [dist_eq_norm_vsub V _ x]

@[simp]

中文:
定理 dist_vadd_left
  条件: (v : V) (x : P)
  结论: dist (v +ᵥ x) x = ‖v‖
  证明: by
  simp [dist_eq_norm_vsub V _ x]

@[simp]

Depends on / 依赖: dist_eq_norm_vsub
-/
theorem dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ‖v‖ := by
  simp [dist_eq_norm_vsub V _ x]

@[simp]
/--
theorem `nndist_vadd_left` / 定理 `nndist_vadd_left`

English:
theorem nndist_vadd_left
  given: (v : V) (x : P)
  statement: nndist (v +ᵥ x) x = ‖v‖₊
  proof: NNReal.eq dist_vadd_left _ _

@[simp]

中文:
定理 nndist_vadd_left
  条件: (v : V) (x : P)
  结论: nndist (v +ᵥ x) x = ‖v‖₊
  证明: NNReal.eq dist_vadd_left _ _

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, dist_vadd_left
-/
theorem nndist_vadd_left (v : V) (x : P) : nndist (v +ᵥ x) x = ‖v‖₊ :=
NNReal.eq dist_vadd_left _ _

@[simp]
/--
theorem `dist_vadd_right` / 定理 `dist_vadd_right`

English:
theorem dist_vadd_right
  given: (v : V) (x : P)
  statement: dist x (v +ᵥ x) = ‖v‖
  proof: by rw [dist_comm, dist_vadd_left]

@[simp]

中文:
定理 dist_vadd_right
  条件: (v : V) (x : P)
  结论: dist x (v +ᵥ x) = ‖v‖
  证明: by rw [dist_comm, dist_vadd_left]

@[simp]

Depends on / 依赖: dist_comm, dist_vadd_left
-/
theorem dist_vadd_right (v : V) (x : P) : dist x (v +ᵥ x) = ‖v‖ := by rw [dist_comm, dist_vadd_left]

@[simp]
/--
theorem `nndist_vadd_right` / 定理 `nndist_vadd_right`

English:
theorem nndist_vadd_right
  given: (v : V) (x : P)
  statement: nndist x (v +ᵥ x) = ‖v‖₊
  proof: NNReal.eq dist_vadd_right _ _

中文:
定理 nndist_vadd_right
  条件: (v : V) (x : P)
  结论: nndist x (v +ᵥ x) = ‖v‖₊
  证明: NNReal.eq dist_vadd_right _ _

Depends on / 依赖: NNReal, NNReal.eq, dist_vadd_right
-/
theorem nndist_vadd_right (v : V) (x : P) : nndist x (v +ᵥ x) = ‖v‖₊ :=
NNReal.eq dist_vadd_right _ _

/-- Isometry between the tangent space `V` of a (semi)normed add torsor `P` and `P` given by
addition/subtraction of `x : P`. -/
@[simps!]
/--
Definition of `IsometryEquiv.vaddConst` / `IsometryEquiv.vaddConst` 的定义

English:
definition IsometryEquiv.vaddConst
  signature: (x : P)
  body: Equiv.vaddConst x
  isometry_toFun := Isometry.of_dist_eq fun _ _ => dist_vadd_cancel_right _ _ _

@[simp]

中文:
定义 等距等价.vaddConst
  签名: (x : P)
  定义体: Equiv.vaddConst x
  isometry_toFun := Isometry.of_dist_eq fun _ _ => dist_vadd_cancel_right _ _ _

@[simp]

Depends on / 依赖: Equiv.vaddConst, vaddConst
-/
def IsometryEquiv.vaddConst (x : P) : V ≃ᵢ P where
  toEquiv := Equiv.vaddConst x
  isometry_toFun := Isometry.of_dist_eq fun _ _ => dist_vadd_cancel_right _ _ _

@[simp]
/--
theorem `dist_vsub_cancel_left` / 定理 `dist_vsub_cancel_left`

English:
theorem dist_vsub_cancel_left
  given: (x y z : P)
  statement: dist (x -ᵥ y) (x -ᵥ z) = dist y z
  proof: by
  rw [dist_eq_norm]; rw [vsub_sub_vsub_cancel_left]; rw [dist_comm]; rw [dist_eq_norm_vsub V]

@[simp]

中文:
定理 dist_vsub_cancel_left
  条件: (x y z : P)
  结论: dist (x -ᵥ y) (x -ᵥ z) = dist y z
  证明: by
  rw [dist_eq_norm]; rw [vsub_sub_vsub_cancel_left]; rw [dist_comm]; rw [dist_eq_norm_vsub V]

@[simp]

Depends on / 依赖: dist_comm, dist_eq_norm, dist_eq_norm_vsub, vsub_sub_vsub_cancel_left
-/
theorem dist_vsub_cancel_left (x y z : P) : dist (x -ᵥ y) (x -ᵥ z) = dist y z := by
  rw [dist_eq_norm]; rw [vsub_sub_vsub_cancel_left]; rw [dist_comm]; rw [dist_eq_norm_vsub V]

@[simp]
/--
theorem `nndist_vsub_cancel_left` / 定理 `nndist_vsub_cancel_left`

English:
theorem nndist_vsub_cancel_left
  given: (x y z : P)
  statement: nndist (x -ᵥ y) (x -ᵥ z) = nndist y z
  proof: NNReal.eq dist_vsub_cancel_left _ _ _

中文:
定理 nndist_vsub_cancel_left
  条件: (x y z : P)
  结论: nndist (x -ᵥ y) (x -ᵥ z) = nndist y z
  证明: NNReal.eq dist_vsub_cancel_left _ _ _

Depends on / 依赖: NNReal, NNReal.eq, dist_vsub_cancel_left
-/
theorem nndist_vsub_cancel_left (x y z : P) : nndist (x -ᵥ y) (x -ᵥ z) = nndist y z :=
NNReal.eq dist_vsub_cancel_left _ _ _

/-- Isometry between the tangent space `V` of a (semi)normed add torsor `P` and `P` given by
subtraction from `x : P`. -/
@[simps!]
/--
Definition of `IsometryEquiv.constVSub` / `IsometryEquiv.constVSub` 的定义

English:
definition IsometryEquiv.constVSub
  signature: (x : P)
  body: Equiv.constVSub x
  isometry_toFun := Isometry.of_dist_eq fun _ _ => dist_vsub_cancel_left _ _ _

@[simp]

中文:
定义 等距等价.constVSub
  签名: (x : P)
  定义体: Equiv.constVSub x
  isometry_toFun := Isometry.of_dist_eq fun _ _ => dist_vsub_cancel_left _ _ _

@[simp]

Depends on / 依赖: Equiv.constVSub, constVSub
-/
def IsometryEquiv.constVSub (x : P) : P ≃ᵢ V where
  toEquiv := Equiv.constVSub x
  isometry_toFun := Isometry.of_dist_eq fun _ _ => dist_vsub_cancel_left _ _ _

@[simp]
/--
theorem `dist_vsub_cancel_right` / 定理 `dist_vsub_cancel_right`

English:
theorem dist_vsub_cancel_right
  given: (x y z : P)
  statement: dist (x -ᵥ z) (y -ᵥ z) = dist x y
  proof: (IsometryEquiv.vaddConst z).symm.dist_eq x y

@[simp]

中文:
定理 dist_vsub_cancel_right
  条件: (x y z : P)
  结论: dist (x -ᵥ z) (y -ᵥ z) = dist x y
  证明: (IsometryEquiv.vaddConst z).symm.dist_eq x y

@[simp]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.vaddConst, dist_eq, symm.dist_eq, vaddConst
-/
theorem dist_vsub_cancel_right (x y z : P) : dist (x -ᵥ z) (y -ᵥ z) = dist x y :=
  (IsometryEquiv.vaddConst z).symm.dist_eq x y

@[simp]
/--
theorem `nndist_vsub_cancel_right` / 定理 `nndist_vsub_cancel_right`

English:
theorem nndist_vsub_cancel_right
  given: (x y z : P)
  statement: nndist (x -ᵥ z) (y -ᵥ z) = nndist x y
  proof: NNReal.eq dist_vsub_cancel_right _ _ _

中文:
定理 nndist_vsub_cancel_right
  条件: (x y z : P)
  结论: nndist (x -ᵥ z) (y -ᵥ z) = nndist x y
  证明: NNReal.eq dist_vsub_cancel_right _ _ _

Depends on / 依赖: NNReal, NNReal.eq, dist_vsub_cancel_right
-/
theorem nndist_vsub_cancel_right (x y z : P) : nndist (x -ᵥ z) (y -ᵥ z) = nndist x y :=
NNReal.eq dist_vsub_cancel_right _ _ _

/--
theorem `dist_vadd_vadd_le` / 定理 `dist_vadd_vadd_le`

English:
theorem dist_vadd_vadd_le
  given: (v v' : V) (p p' : P)
  proof: by
  simpa using dist_triangle (v +ᵥ p) (v' +ᵥ p) (v' +ᵥ p')

中文:
定理 dist_vadd_vadd_le
  条件: (v v' : V) (p p' : P)
  证明: by
  simpa using dist_triangle (v +ᵥ p) (v' +ᵥ p) (v' +ᵥ p')

Depends on / 依赖: dist_triangle
-/
theorem dist_vadd_vadd_le (v v' : V) (p p' : P) :
    dist (v +ᵥ p) (v' +ᵥ p') <= dist v v' + dist p p' := by
  simpa using dist_triangle (v +ᵥ p) (v' +ᵥ p) (v' +ᵥ p')

/--
theorem `nndist_vadd_vadd_le` / 定理 `nndist_vadd_vadd_le`

English:
theorem nndist_vadd_vadd_le
  given: (v v' : V) (p p' : P)
  proof: dist_vadd_vadd_le _ _ _ _

中文:
定理 nndist_vadd_vadd_le
  条件: (v v' : V) (p p' : P)
  证明: dist_vadd_vadd_le _ _ _ _

Depends on / 依赖: dist_vadd_vadd_le
-/
theorem nndist_vadd_vadd_le (v v' : V) (p p' : P) :
    nndist (v +ᵥ p) (v' +ᵥ p') <= nndist v v' + nndist p p' :=
  dist_vadd_vadd_le _ _ _ _

/--
theorem `dist_vsub_vsub_le` / 定理 `dist_vsub_vsub_le`

English:
theorem dist_vsub_vsub_le
  given: (p₁ p₂ p₃ p₄ : P)
  proof: by
  rw [dist_eq_norm]; rw [vsub_sub_vsub_comm]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]
  exact norm_sub_le _ _

中文:
定理 dist_vsub_vsub_le
  条件: (p₁ p₂ p₃ p₄ : P)
  证明: by
  rw [dist_eq_norm]; rw [vsub_sub_vsub_comm]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]
  exact norm_sub_le _ _

Depends on / 依赖: dist_eq_norm, dist_eq_norm_vsub, norm_sub_le, vsub_sub_vsub_comm
-/
theorem dist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
    dist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) <= dist p₁ p₃ + dist p₂ p₄ := by
  rw [dist_eq_norm]; rw [vsub_sub_vsub_comm]; rw [dist_eq_norm_vsub V]; rw [dist_eq_norm_vsub V]
  exact norm_sub_le _ _

/--
theorem `nndist_vsub_vsub_le` / 定理 `nndist_vsub_vsub_le`

English:
theorem nndist_vsub_vsub_le
  given: (p₁ p₂ p₃ p₄ : P)
  proof: by
  simp only [← NNReal.coe_le_coe, NNReal.coe_add, ← dist_nndist, dist_vsub_vsub_le]

中文:
定理 nndist_vsub_vsub_le
  条件: (p₁ p₂ p₃ p₄ : P)
  证明: by
  simp only [← NNReal.coe_le_coe, NNReal.coe_add, ← dist_nndist, dist_vsub_vsub_le]

Depends on / 依赖: NNReal, NNReal.coe_add, NNReal.coe_le_coe, coe_add, coe_le_coe, dist_nndist, dist_vsub_vsub_le
-/
theorem nndist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
    nndist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) <= nndist p₁ p₃ + nndist p₂ p₄ := by
  simp only [← NNReal.coe_le_coe, NNReal.coe_add, ← dist_nndist, dist_vsub_vsub_le]

/--
theorem `edist_vadd_vadd_le` / 定理 `edist_vadd_vadd_le`

English:
theorem edist_vadd_vadd_le
  given: (v v' : V) (p p' : P)
  proof: by
  simp only [edist_nndist]
  norm_cast
  apply dist_vadd_vadd_le

中文:
定理 edist_vadd_vadd_le
  条件: (v v' : V) (p p' : P)
  证明: by
  simp only [edist_nndist]
  norm_cast
  apply dist_vadd_vadd_le

Depends on / 依赖: dist_vadd_vadd_le, edist_nndist
-/
theorem edist_vadd_vadd_le (v v' : V) (p p' : P) :
    edist (v +ᵥ p) (v' +ᵥ p') <= edist v v' + edist p p' := by
  simp only [edist_nndist]
  norm_cast
  apply dist_vadd_vadd_le

/--
theorem `edist_vsub_vsub_le` / 定理 `edist_vsub_vsub_le`

English:
theorem edist_vsub_vsub_le
  given: (p₁ p₂ p₃ p₄ : P)
  proof: by
  simp only [edist_nndist]
  norm_cast
  apply dist_vsub_vsub_le

中文:
定理 edist_vsub_vsub_le
  条件: (p₁ p₂ p₃ p₄ : P)
  证明: by
  simp only [edist_nndist]
  norm_cast
  apply dist_vsub_vsub_le

Depends on / 依赖: dist_vsub_vsub_le, edist_nndist
-/
theorem edist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
    edist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) <= edist p₁ p₃ + edist p₂ p₄ := by
  simp only [edist_nndist]
  norm_cast
  apply dist_vsub_vsub_le

/-- The pseudodistance defines a pseudometric space structure on the torsor. This
is not an instance because it depends on `V` to define a `MetricSpace P`. -/
@[instance_reducible]
/--
Definition of `pseudoMetricSpaceOfNormedAddCommGroupOfAddTorsor` / `pseudoMetricSpaceOfNormedAddCommGroupOfAddTorsor` 的定义

English:
definition pseudoMetricSpaceOfNormedAddCommGroupOfAddTorsor
  signature: (V P : Type*) [SeminormedAddCommGroup V]
  body: ‖(x -ᵥ y : V)‖
  dist_self x := by simp
  dist_comm x y := by simp only [← neg_vsub_eq_vsub_rev y x, norm_neg]
  dist_triangle x y z := by
    rw [← vsub_add_vsub_cancel]
    apply norm_add_le

中文:
定义 pseudoMetricSpaceOfNormedAddCommGroupOfAddTorsor
  签名: (V P : 类型) [SeminormedAddComm群 V]
  定义体: ‖(x -ᵥ y : V)‖
  dist_self x := by simp
  dist_comm x y := by simp only [← neg_vsub_eq_vsub_rev y x, norm_neg]
  dist_triangle x y z := by
    rw [← vsub_add_vsub_cancel]
    apply norm_add_le
-/
def pseudoMetricSpaceOfNormedAddCommGroupOfAddTorsor (V P : Type*) [SeminormedAddCommGroup V]
    [AddTorsor V P] : PseudoMetricSpace P where
  dist x y := ‖(x -ᵥ y : V)‖
  dist_self x := by simp
  dist_comm x y := by simp only [← neg_vsub_eq_vsub_rev y x, norm_neg]
  dist_triangle x y z := by
    rw [← vsub_add_vsub_cancel]
    apply norm_add_le

/-- The distance defines a metric space structure on the torsor. This
is not an instance because it depends on `V` to define a `MetricSpace P`. -/
@[instance_reducible]
/--
Definition of `metricSpaceOfNormedAddCommGroupOfAddTorsor` / `metricSpaceOfNormedAddCommGroupOfAddTorsor` 的定义

English:
definition metricSpaceOfNormedAddCommGroupOfAddTorsor
  signature: (V P : Type*) [NormedAddCommGroup V]
  body: ‖(x -ᵥ y : V)‖
  dist_self x := by simp
  eq_of_dist_eq_zero h := by simpa using h
  dist_comm x y := by simp only [← neg_vsub_eq_vsub_rev y x, norm_neg]
  dist_triangle x y z := by
    rw [← vsub_add_vsub_cancel]
    apply norm_add_le

中文:
定义 metricSpaceOfNormedAddCommGroupOfAddTorsor
  签名: (V P : 类型) [赋范交换加群 V]
  定义体: ‖(x -ᵥ y : V)‖
  dist_self x := by simp
  eq_of_dist_eq_zero h := by simpa using h
  dist_comm x y := by simp only [← neg_vsub_eq_vsub_rev y x, norm_neg]
  dist_triangle x y z := by
    rw [← vsub_add_vsub_cancel]
    apply norm_add_le
-/
def metricSpaceOfNormedAddCommGroupOfAddTorsor (V P : Type*) [NormedAddCommGroup V]
    [AddTorsor V P] : MetricSpace P where
  dist x y := ‖(x -ᵥ y : V)‖
  dist_self x := by simp
  eq_of_dist_eq_zero h := by simpa using h
  dist_comm x y := by simp only [← neg_vsub_eq_vsub_rev y x, norm_neg]
  dist_triangle x y z := by
    rw [← vsub_add_vsub_cancel]
    apply norm_add_le

/--
theorem `LipschitzWith.vadd` / 定理 `LipschitzWith.vadd`

English:
theorem LipschitzWith.vadd
  statement: [PseudoEMetricSpace α] {f : α -> V} {g : α -> P} {Kf Kg : Real>=0}
  proof: fun x y =>
  calc
    edist (f x +ᵥ g x) (f y +ᵥ g y) <= edist (f x) (f y) + edist (g x) (g y) :=
      edist_vadd_vadd_le _ _ _ _
    _ <= Kf * edist x y + Kg * edist x y := add_le_add (hf x y) (hg x y)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm

中文:
定理 LipschitzWith.vadd
  结论: [PseudoEMetric空间 α] {f : α -> V} {g : α -> P} {Kf Kg : 实数>=0}
  证明: fun x y =>
  calc
    edist (f x +ᵥ g x) (f y +ᵥ g y) <= edist (f x) (f y) + edist (g x) (g y) :=
      edist_vadd_vadd_le _ _ _ _
    _ <= Kf * edist x y + Kg * edist x y := add_le_add (hf x y) (hg x y)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm

Depends on / 依赖: add_le_add, add_mul, edist_vadd_vadd_le
-/
theorem LipschitzWith.vadd [PseudoEMetricSpace α] {f : α -> V} {g : α -> P} {Kf Kg : Real>=0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf + Kg) (f +ᵥ g) :=
  fun x y =>
  calc
    edist (f x +ᵥ g x) (f y +ᵥ g y) <= edist (f x) (f y) + edist (g x) (g y) :=
      edist_vadd_vadd_le _ _ _ _
    _ <= Kf * edist x y + Kg * edist x y := add_le_add (hf x y) (hg x y)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm

/--
theorem `LipschitzWith.vsub` / 定理 `LipschitzWith.vsub`

English:
theorem LipschitzWith.vsub
  statement: [PseudoEMetricSpace α] {f g : α -> P} {Kf Kg : Real>=0}
  proof: fun x y =>
  calc
    edist (f x -ᵥ g x) (f y -ᵥ g y) <= edist (f x) (f y) + edist (g x) (g y) :=
      edist_vsub_vsub_le _ _ _ _
    _ <= Kf * edist x y + Kg * edist x y := add_le_add (hf x y) (hg x y)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm

@[fun_prop]

中文:
定理 LipschitzWith.vsub
  结论: [PseudoEMetric空间 α] {f g : α -> P} {Kf Kg : 实数>=0}
  证明: fun x y =>
  calc
    edist (f x -ᵥ g x) (f y -ᵥ g y) <= edist (f x) (f y) + edist (g x) (g y) :=
      edist_vsub_vsub_le _ _ _ _
    _ <= Kf * edist x y + Kg * edist x y := add_le_add (hf x y) (hg x y)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm

@[fun_prop]

Depends on / 依赖: add_le_add, add_mul, edist_vsub_vsub_le
-/
theorem LipschitzWith.vsub [PseudoEMetricSpace α] {f g : α -> P} {Kf Kg : Real>=0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf + Kg) (f -ᵥ g) :=
  fun x y =>
  calc
    edist (f x -ᵥ g x) (f y -ᵥ g y) <= edist (f x) (f y) + edist (g x) (g y) :=
      edist_vsub_vsub_le _ _ _ _
    _ <= Kf * edist x y + Kg * edist x y := add_le_add (hf x y) (hg x y)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm

@[fun_prop]
/--
theorem `uniformContinuous_vadd` / 定理 `uniformContinuous_vadd`

English:
theorem uniformContinuous_vadd
  statement: UniformContinuous fun x : V × P => x.1 +ᵥ x.2
  proof: (LipschitzWith.prod_fst.vadd LipschitzWith.prod_snd).uniformContinuous

@[fun_prop]

中文:
定理 uniformContinuous_vadd
  结论: 一致连续 fun x : V × P => x.1 +ᵥ x.2
  证明: (LipschitzWith.prod_fst.vadd LipschitzWith.prod_snd).uniformContinuous

@[fun_prop]

Depends on / 依赖: LipschitzWith, LipschitzWith.prod_fst.vadd, LipschitzWith.prod_snd, prod_fst, prod_snd, uniformContinuous
-/
theorem uniformContinuous_vadd : UniformContinuous fun x : V × P => x.1 +ᵥ x.2 :=
  (LipschitzWith.prod_fst.vadd LipschitzWith.prod_snd).uniformContinuous

@[fun_prop]
/--
theorem `uniformContinuous_vsub` / 定理 `uniformContinuous_vsub`

English:
theorem uniformContinuous_vsub
  statement: UniformContinuous fun x : P × P => x.1 -ᵥ x.2
  proof: (LipschitzWith.prod_fst.vsub LipschitzWith.prod_snd).uniformContinuous

中文:
定理 uniformContinuous_vsub
  结论: 一致连续 fun x : P × P => x.1 -ᵥ x.2
  证明: (LipschitzWith.prod_fst.vsub LipschitzWith.prod_snd).uniformContinuous

Depends on / 依赖: LipschitzWith, LipschitzWith.prod_fst.vsub, LipschitzWith.prod_snd, prod_fst, prod_snd, uniformContinuous
-/
theorem uniformContinuous_vsub : UniformContinuous fun x : P × P => x.1 -ᵥ x.2 :=
  (LipschitzWith.prod_fst.vsub LipschitzWith.prod_snd).uniformContinuous

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalAddTorsor P
  body: uniformContinuous_vadd.continuous
  continuous_vsub := uniformContinuous_vsub.continuous

中文:
实例 :
  签名: 是TopologicalAddTorsor P
  定义体: uniformContinuous_vadd.continuous
  continuous_vsub := uniformContinuous_vsub.continuous

Depends on / 依赖: continuous, uniformContinuous_vadd, uniformContinuous_vadd.continuous
-/
instance : IsTopologicalAddTorsor P where
  continuous_vadd := uniformContinuous_vadd.continuous
  continuous_vsub := uniformContinuous_vsub.continuous

/--
Definition of `Function.Injective.normedAddTorsor` / `Function.Injective.normedAddTorsor` 的定义

English:
abbreviation Function.Injective.normedAddTorsor
  signature: {Q : Type*} [VAdd V Q] [VSub V Q]
  body: hf.addTorsor f vadd vsub
  dist_eq_norm' x y := by simp [norm, NormedAddTorsor.dist_eq_norm', vsub]

中文:
缩写 函数.单射.normedAddTorsor
  签名: {Q : 类型} [向量加法 V Q] [向量减法 V Q]
  定义体: hf.addTorsor f vadd vsub
  dist_eq_norm' x y := by simp [norm, NormedAddTorsor.dist_eq_norm', vsub]

Depends on / 依赖: addTorsor, hf.addTorsor
-/
abbrev Function.Injective.normedAddTorsor {Q : Type*} [VAdd V Q] [VSub V Q]
    [Nonempty Q] [PseudoMetricSpace Q] (f : Q -> P) (hf : Function.Injective f)
    (vadd : forall (c : V) (x : Q), f (c +ᵥ x) = c +ᵥ f x)
    (vsub : forall (x y : Q), x -ᵥ y = f x -ᵥ f y)
    (norm : forall (x y : Q), dist x y = dist (f x) (f y)) : NormedAddTorsor V Q where
  __ := hf.addTorsor f vadd vsub
  dist_eq_norm' x y := by simp [norm, NormedAddTorsor.dist_eq_norm', vsub]

/--
Definition of `Function.Surjective.normedAddTorsor` / `Function.Surjective.normedAddTorsor` 的定义

English:
abbreviation Function.Surjective.normedAddTorsor
  body: hf.addTorsor f vadd vsub
  dist_eq_norm' := by simp [hf.forall, ← norm, NormedAddTorsor.dist_eq_norm', ← vsub]

中文:
缩写 函数.满射.normedAddTorsor
  定义体: hf.addTorsor f vadd vsub
  dist_eq_norm' := by simp [hf.forall, ← norm, NormedAddTorsor.dist_eq_norm', ← vsub]

Depends on / 依赖: addTorsor, hf.addTorsor
-/
abbrev Function.Surjective.normedAddTorsor
    {Q : Type*} [VAdd V Q] [VSub V Q] [PseudoMetricSpace Q]
    (f : P -> Q) (hf : Surjective f)
    (vadd : forall (c : V) (x : P), f (c +ᵥ x) = c +ᵥ f x)
    (vsub : forall (x y : P), x -ᵥ y = f x -ᵥ f y)
    (norm : forall (x y : P), dist x y = dist (f x) (f y)) : NormedAddTorsor V Q where
  __ := hf.addTorsor f vadd vsub
  dist_eq_norm' := by simp [hf.forall, ← norm, NormedAddTorsor.dist_eq_norm', ← vsub]
