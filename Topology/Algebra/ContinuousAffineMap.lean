/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Affine

/-!
# Continuous affine maps.

This file defines a type of bundled continuous affine maps.

## Main definitions:

* `ContinuousAffineMap`

## Notation:

We introduce the notation `P →ᴬ[R] Q` for `ContinuousAffineMap R P Q` (not to be confused with the
notation `A →A[R] B` for `ContinuousAlgHom`). Note that this is parallel to the notation `E →L[R] F`
for `ContinuousLinearMap R E F`.
-/

@[expose] public section


/--
Definition of `ContinuousAffineMap` / `ContinuousAffineMap` 的定义

English:
structure ContinuousAffineMap
  parameters: (R : Type*) {V W : Type*} (P Q : Type*) [Ring R] [AddCommGroup V]
  extends: P ->ᵃ[R] Q
  axioms and operations (1):
    - cont : Continuous toFun

中文:
结构 余ntinuousAffine映射
  参数: (R : 类型) {V W : 类型} (P Q : 类型) [环 R] [加法交换群 V]
  继承: P ->ᵃ[R] Q
  公理与运算 (1 个):
    - cont : 连续 toFun
-/
structure ContinuousAffineMap (R : Type*) {V W : Type*} (P Q : Type*) [Ring R] [AddCommGroup V]
  [Module R V] [TopologicalSpace P] [AddTorsor V P] [AddCommGroup W] [Module R W]
  [TopologicalSpace Q] [AddTorsor W Q] extends P ->ᵃ[R] Q where
  cont : Continuous toFun

/-- A continuous map of affine spaces -/
notation:25 P " ->ᴬ[" R "] " Q => ContinuousAffineMap R P Q

namespace ContinuousAffineMap

variable {R V W P Q : Type*} [Ring R]
variable [AddCommGroup V] [Module R V] [TopologicalSpace P] [AddTorsor V P]
variable [AddCommGroup W] [Module R W] [TopologicalSpace Q] [AddTorsor W Q]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (P ->ᴬ[R] Q) (P ->ᵃ[R] Q)
  body: ⟨toAffineMap⟩

中文:
实例 :
  签名: Coe (P ->ᴬ[R] Q) (P ->ᵃ[R] Q)
  定义体: ⟨toAffineMap⟩

Depends on / 依赖: toAffineMap
-/
instance : Coe (P ->ᴬ[R] Q) (P ->ᵃ[R] Q) :=
  ⟨toAffineMap⟩

attribute [coe] ContinuousAffineMap.toAffineMap

/--
theorem `toAffineMap_injective` / 定理 `toAffineMap_injective`

English:
theorem toAffineMap_injective
  given: {f g : P ->ᴬ[R] Q} (h : (f : P ->ᵃ[R] Q) = (g : P ->ᵃ[R] Q))
  proof: by
  cases f
  cases g
  congr

中文:
定理 toAffineMap_injective
  条件: {f g : P ->ᴬ[R] Q} (h : (f : P ->ᵃ[R] Q) = (g : P ->ᵃ[R] Q))
  证明: by
  cases f
  cases g
  congr
-/
theorem toAffineMap_injective {f g : P ->ᴬ[R] Q} (h : (f : P ->ᵃ[R] Q) = (g : P ->ᵃ[R] Q)) :
    f = g := by
  cases f
  cases g
  congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (P ->ᴬ[R] Q) P Q
  body: f.toAffineMap
coe_injective _ _ h := toAffineMap_injective DFunLike.coe_injective h

中文:
实例 :
  签名: 函数状 (P ->ᴬ[R] Q) P Q
  定义体: f.toAffineMap
coe_injective _ _ h := toAffineMap_injective DFunLike.coe_injective h

Depends on / 依赖: f.toAffineMap, toAffineMap
-/
instance : FunLike (P ->ᴬ[R] Q) P Q where
  coe f := f.toAffineMap
coe_injective _ _ h := toAffineMap_injective DFunLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousMapClass (P ->ᴬ[R] Q) P Q
  body: cont

中文:
实例 :
  签名: 连续映射类 (P ->ᴬ[R] Q) P Q
  定义体: cont
-/
instance : ContinuousMapClass (P ->ᴬ[R] Q) P Q where
  map_continuous := cont

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : P ->ᴬ[R] Q)
  statement: f.toFun = ⇑f
  proof: rfl

中文:
定理 toFun_eq_coe
  条件: (f : P ->ᴬ[R] Q)
  结论: f.toFun = ⇑f
  证明: rfl
-/
theorem toFun_eq_coe (f : P ->ᴬ[R] Q) : f.toFun = ⇑f := rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Function.Injective (P ->ᴬ[R] Q) (P -> Q) (⇑)
  proof: DFunLike.coe_injective

@[ext]

中文:
定理 coe_injective
  结论: @函数.单射 (P ->ᴬ[R] Q) (P -> Q) (⇑)
  证明: DFunLike.coe_injective

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective : @Function.Injective (P ->ᴬ[R] Q) (P -> Q) (⇑) :=
  DFunLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : P ->ᴬ[R] Q} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {f g : P ->ᴬ[R] Q} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : P ->ᴬ[R] Q} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : P ->ᴬ[R] Q} (h : f = g) (x : P)
  statement: f x = g x
  proof: DFunLike.congr_fun h _

中文:
定理 congr_fun
  条件: {f g : P ->ᴬ[R] Q} (h : f = g) (x : P)
  结论: f x = g x
  证明: DFunLike.congr_fun h _

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
theorem congr_fun {f g : P ->ᴬ[R] Q} (h : f = g) (x : P) : f x = g x :=
  DFunLike.congr_fun h _

/--
Definition of `toContinuousMap` / `toContinuousMap` 的定义

English:
definition toContinuousMap
  signature: (f : P ->ᴬ[R] Q)
  body: ⟨f, f.cont⟩

中文:
定义 toContinuousMap
  签名: (f : P ->ᴬ[R] Q)
  定义体: ⟨f, f.cont⟩

Depends on / 依赖: f.cont
-/
def toContinuousMap (f : P ->ᴬ[R] Q) : C(P, Q) :=
  ⟨f, f.cont⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeHead (P ->ᴬ[R] Q) C(P, Q)
  body: ⟨toContinuousMap⟩

@[simp]

中文:
实例 :
  签名: CoeHead (P ->ᴬ[R] Q) C(P, Q)
  定义体: ⟨toContinuousMap⟩

@[simp]

Depends on / 依赖: toContinuousMap
-/
instance : CoeHead (P ->ᴬ[R] Q) C(P, Q) :=
  ⟨toContinuousMap⟩

@[simp]
/--
theorem `toContinuousMap_coe` / 定理 `toContinuousMap_coe`

English:
theorem toContinuousMap_coe
  given: (f : P ->ᴬ[R] Q)
  statement: f.toContinuousMap = ↑f
  proof: rfl

@[simp, norm_cast]

中文:
定理 toContinuousMap_coe
  条件: (f : P ->ᴬ[R] Q)
  结论: f.toContinuousMap = ↑f
  证明: rfl

@[simp, norm_cast]
-/
theorem toContinuousMap_coe (f : P ->ᴬ[R] Q) : f.toContinuousMap = ↑f := rfl

@[simp, norm_cast]
/--
theorem `coe_toAffineMap` / 定理 `coe_toAffineMap`

English:
theorem coe_toAffineMap
  given: (f : P ->ᴬ[R] Q)
  statement: ((f : P ->ᵃ[R] Q) : P -> Q) = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_toAffineMap
  条件: (f : P ->ᴬ[R] Q)
  结论: ((f : P ->ᵃ[R] Q) : P -> Q) = f
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_toAffineMap (f : P ->ᴬ[R] Q) : ((f : P ->ᵃ[R] Q) : P -> Q) = f := rfl

@[simp, norm_cast]
/--
theorem `coe_to_continuousMap` / 定理 `coe_to_continuousMap`

English:
theorem coe_to_continuousMap
  given: (f : P ->ᴬ[R] Q)
  statement: ((f : C(P, Q)) : P -> Q) = f
  proof: rfl

中文:
定理 coe_to_continuousMap
  条件: (f : P ->ᴬ[R] Q)
  结论: ((f : C(P, Q)) : P -> Q) = f
  证明: rfl
-/
theorem coe_to_continuousMap (f : P ->ᴬ[R] Q) : ((f : C(P, Q)) : P -> Q) = f := rfl

/--
theorem `to_continuousMap_injective` / 定理 `to_continuousMap_injective`

English:
theorem to_continuousMap_injective
  given: {f g : P ->ᴬ[R] Q} (h : (f : C(P, Q)) = (g : C(P, Q)))
  proof: by
  ext a
  exact ContinuousMap.congr_fun h a

@[norm_cast]

中文:
定理 to_continuousMap_injective
  条件: {f g : P ->ᴬ[R] Q} (h : (f : C(P, Q)) = (g : C(P, Q)))
  证明: by
  ext a
  exact ContinuousMap.congr_fun h a

@[norm_cast]

Depends on / 依赖: ContinuousMap, ContinuousMap.congr_fun, congr_fun
-/
theorem to_continuousMap_injective {f g : P ->ᴬ[R] Q} (h : (f : C(P, Q)) = (g : C(P, Q))) :
    f = g := by
  ext a
  exact ContinuousMap.congr_fun h a

@[norm_cast]
/--
theorem `coe_toAffineMap_mk` / 定理 `coe_toAffineMap_mk`

English:
theorem coe_toAffineMap_mk
  given: (f : P ->ᵃ[R] Q) (h)
  statement: ((⟨f, h⟩ : P ->ᴬ[R] Q) : P ->ᵃ[R] Q) = f
  proof: rfl

@[norm_cast]

中文:
定理 coe_toAffineMap_mk
  条件: (f : P ->ᵃ[R] Q) (h)
  结论: ((⟨f, h⟩ : P ->ᴬ[R] Q) : P ->ᵃ[R] Q) = f
  证明: rfl

@[norm_cast]
-/
theorem coe_toAffineMap_mk (f : P ->ᵃ[R] Q) (h) : ((⟨f, h⟩ : P ->ᴬ[R] Q) : P ->ᵃ[R] Q) = f := rfl

@[norm_cast]
/--
theorem `coe_continuousMap_mk` / 定理 `coe_continuousMap_mk`

English:
theorem coe_continuousMap_mk
  given: (f : P ->ᵃ[R] Q) (h)
  statement: ((⟨f, h⟩ : P ->ᴬ[R] Q) : C(P, Q)) = ⟨f, h⟩
  proof: rfl

@[simp]

中文:
定理 coe_continuousMap_mk
  条件: (f : P ->ᵃ[R] Q) (h)
  结论: ((⟨f, h⟩ : P ->ᴬ[R] Q) : C(P, Q)) = ⟨f, h⟩
  证明: rfl

@[simp]
-/
theorem coe_continuousMap_mk (f : P ->ᵃ[R] Q) (h) : ((⟨f, h⟩ : P ->ᴬ[R] Q) : C(P, Q)) = ⟨f, h⟩ := rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : P ->ᵃ[R] Q) (h)
  statement: ((⟨f, h⟩ : P ->ᴬ[R] Q) : P -> Q) = f
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (f : P ->ᵃ[R] Q) (h)
  结论: ((⟨f, h⟩ : P ->ᴬ[R] Q) : P -> Q) = f
  证明: rfl

@[simp]
-/
theorem coe_mk (f : P ->ᵃ[R] Q) (h) : ((⟨f, h⟩ : P ->ᴬ[R] Q) : P -> Q) = f := rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : P ->ᴬ[R] Q) (h)
  statement: (⟨(f : P ->ᵃ[R] Q), h⟩ : P ->ᴬ[R] Q) = f
  proof: by
  ext
  rfl

@[continuity]

中文:
定理 mk_coe
  条件: (f : P ->ᴬ[R] Q) (h)
  结论: (⟨(f : P ->ᵃ[R] Q), h⟩ : P ->ᴬ[R] Q) = f
  证明: by
  ext
  rfl

@[continuity]
-/
theorem mk_coe (f : P ->ᴬ[R] Q) (h) : (⟨(f : P ->ᵃ[R] Q), h⟩ : P ->ᴬ[R] Q) = f := by
  ext
  rfl

@[continuity]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (f : P ->ᴬ[R] Q)
  statement: Continuous f
  proof: f.2

中文:
定理 continuous
  条件: (f : P ->ᴬ[R] Q)
  结论: 连续 f
  证明: f.2
-/
protected theorem continuous (f : P ->ᴬ[R] Q) : Continuous f := f.2

variable (R P)

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (q : Q)
  body: { AffineMap.const R P q with cont := continuous_const }

@[simp]

中文:
定义 const
  签名: (q : Q)
  定义体: { AffineMap.const R P q with cont := continuous_const }

@[simp]

Depends on / 依赖: AffineMap, AffineMap.const, continuous_const
-/
def const (q : Q) : P ->ᴬ[R] Q :=
  { AffineMap.const R P q with cont := continuous_const }

@[simp]
/--
theorem `coe_const` / 定理 `coe_const`

English:
theorem coe_const
  given: (q : Q)
  statement: ⇑(const R P q) = Function.const P q
  proof: rfl

中文:
定理 coe_const
  条件: (q : Q)
  结论: ⇑(const R P q) = 函数.const P q
  证明: rfl
-/
theorem coe_const (q : Q) : ⇑(const R P q) = Function.const P q := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (P ->ᴬ[R] Q)
  body: ⟨const R P Nonempty.some (by infer_instance : Nonempty Q)⟩

中文:
实例 :
  签名: 可居 (P ->ᴬ[R] Q)
  定义体: ⟨const R P Nonempty.some (by infer_instance : Nonempty Q)⟩

Depends on / 依赖: Nonempty, Nonempty.some, infer_instance
-/
noncomputable instance : Inhabited (P ->ᴬ[R] Q) :=
⟨const R P Nonempty.some (by infer_instance : Nonempty Q)⟩

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : P ->ᴬ[R] P
  body: { AffineMap.id R P with cont := continuous_id }

@[simp, norm_cast]

中文:
定义 id
  签名: : P ->ᴬ[R] P
  定义体: { AffineMap.id R P with cont := continuous_id }

@[simp, norm_cast]

Depends on / 依赖: AffineMap, AffineMap.id, continuous_id
-/
def id : P ->ᴬ[R] P := { AffineMap.id R P with cont := continuous_id }

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(id R P) = _root_.id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(id R P) = _root_.id
  证明: rfl
-/
theorem coe_id : ⇑(id R P) = _root_.id := rfl

variable {R P} {W₂ Q₂ W₃ Q₃ : Type*}
variable [AddCommGroup W₂] [Module R W₂] [TopologicalSpace Q₂] [AddTorsor W₂ Q₂]

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : Q ->ᴬ[R] Q₂) (g : P ->ᴬ[R] Q)
  body: { (f : Q ->ᵃ[R] Q₂).comp (g : P ->ᵃ[R] Q) with cont := f.cont.comp g.cont }

@[simp, norm_cast]

中文:
定义 comp
  签名: (f : Q ->ᴬ[R] Q₂) (g : P ->ᴬ[R] Q)
  定义体: { (f : Q ->ᵃ[R] Q₂).comp (g : P ->ᵃ[R] Q) with cont := f.cont.comp g.cont }

@[simp, norm_cast]

Depends on / 依赖: f.cont.comp, g.cont
-/
def comp (f : Q ->ᴬ[R] Q₂) (g : P ->ᴬ[R] Q) : P ->ᴬ[R] Q₂ :=
  { (f : Q ->ᵃ[R] Q₂).comp (g : P ->ᵃ[R] Q) with cont := f.cont.comp g.cont }

@[simp, norm_cast]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : Q ->ᴬ[R] Q₂) (g : P ->ᴬ[R] Q)
  statement: ⇑(f.comp g) = f ∘ g
  proof: rfl

中文:
定理 coe_comp
  条件: (f : Q ->ᴬ[R] Q₂) (g : P ->ᴬ[R] Q)
  结论: ⇑(f.comp g) = f ∘ g
  证明: rfl
-/
theorem coe_comp (f : Q ->ᴬ[R] Q₂) (g : P ->ᴬ[R] Q) : ⇑(f.comp g) = f ∘ g := rfl

/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : Q ->ᴬ[R] Q₂) (g : P ->ᴬ[R] Q) (p : P)
  statement: f.comp g p = f (g p)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : Q ->ᴬ[R] Q₂) (g : P ->ᴬ[R] Q) (p : P)
  结论: f.comp g p = f (g p)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : Q ->ᴬ[R] Q₂) (g : P ->ᴬ[R] Q) (p : P) : f.comp g p = f (g p) := rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : P ->ᴬ[R] Q)
  statement: f.comp (id R P) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : P ->ᴬ[R] Q)
  结论: f.comp (id R P) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : P ->ᴬ[R] Q) : f.comp (id R P) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : P ->ᴬ[R] Q)
  statement: (id R Q).comp f = f
  proof: ext fun _ => rfl

中文:
定理 id_comp
  条件: (f : P ->ᴬ[R] Q)
  结论: (id R Q).comp f = f
  证明: ext fun _ => rfl
-/
theorem id_comp (f : P ->ᴬ[R] Q) : (id R Q).comp f = f :=
  ext fun _ => rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying a `ContinuousAffineMap` commutes with `AffineMap.lineMap`. -/
@[simp]
/--
theorem `apply_lineMap` / 定理 `apply_lineMap`

English:
theorem apply_lineMap
  given: (f : P ->ᴬ[R] Q) (p₀ p₁ : P) (c : R)
  proof: by
  rw [← ContinuousAffineMap.coe_toAffineMap]; rw [AffineMap.apply_lineMap]

中文:
定理 apply_lineMap
  条件: (f : P ->ᴬ[R] Q) (p₀ p₁ : P) (c : R)
  证明: by
  rw [← ContinuousAffineMap.coe_toAffineMap]; rw [AffineMap.apply_lineMap]

Depends on / 依赖: AffineMap, AffineMap.apply_lineMap, ContinuousAffineMap, ContinuousAffineMap.coe_toAffineMap, apply_lineMap, coe_toAffineMap
-/
theorem apply_lineMap (f : P ->ᴬ[R] Q) (p₀ p₁ : P) (c : R) :
    f (AffineMap.lineMap p₀ p₁ c) = AffineMap.lineMap (f p₀) (f p₁) c := by
  rw [← ContinuousAffineMap.coe_toAffineMap]; rw [AffineMap.apply_lineMap]

/--
Definition of `lineMap` / `lineMap` 的定义

English:
definition lineMap
  signature: (p₀ p₁ : P) [TopologicalSpace R] [TopologicalSpace V]
  body: AffineMap.lineMap p₀ p₁
  cont := (continuous_id.smul continuous_const).vadd continuous_const

中文:
定义 lineMap
  签名: (p₀ p₁ : P) [拓扑空间 R] [拓扑空间 V]
  定义体: AffineMap.lineMap p₀ p₁
  cont := (continuous_id.smul continuous_const).vadd continuous_const

Depends on / 依赖: AffineMap, AffineMap.lineMap, lineMap
-/
def lineMap (p₀ p₁ : P) [TopologicalSpace R] [TopologicalSpace V]
    [ContinuousSMul R V] [ContinuousVAdd V P] : R ->ᴬ[R] P where
  toAffineMap := AffineMap.lineMap p₀ p₁
  cont := (continuous_id.smul continuous_const).vadd continuous_const

/--
lemma `lineMap_toAffineMap` / 引理 `lineMap_toAffineMap`

English:
lemma lineMap_toAffineMap
  statement: (p₀ p₁ : P) [TopologicalSpace R] [TopologicalSpace V]
  proof: rfl

中文:
引理 lineMap_toAffineMap
  结论: (p₀ p₁ : P) [拓扑空间 R] [拓扑空间 V]
  证明: rfl
-/
@[simp] lemma lineMap_toAffineMap (p₀ p₁ : P) [TopologicalSpace R] [TopologicalSpace V]
    [ContinuousSMul R V] [ContinuousVAdd V P] :
    (lineMap p₀ p₁).toAffineMap = AffineMap.lineMap (k := R) p₀ p₁ := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coe_lineMap_eq` / 引理 `coe_lineMap_eq`

English:
lemma coe_lineMap_eq
  statement: (p₀ p₁ : P) [TopologicalSpace R] [TopologicalSpace V]
  proof: rfl

中文:
引理 coe_lineMap_eq
  结论: (p₀ p₁ : P) [拓扑空间 R] [拓扑空间 V]
  证明: rfl
-/
lemma coe_lineMap_eq (p₀ p₁ : P) [TopologicalSpace R] [TopologicalSpace V]
    [ContinuousSMul R V] [ContinuousVAdd V P] :
    ⇑(ContinuousAffineMap.lineMap p₀ p₁) = ⇑(AffineMap.lineMap (k := R) p₀ p₁) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying a `ContinuousAffineMap` commutes with `ContinuousAffineMap.lineMap`. -/
@[simp]
/--
theorem `apply_lineMap'` / 定理 `apply_lineMap'`

English:
theorem apply_lineMap'
  statement: [TopologicalSpace R] [TopologicalSpace V] [TopologicalSpace W]
  proof: by
  simp_rw [coe_lineMap_eq, apply_lineMap]

中文:
定理 apply_lineMap'
  结论: [拓扑空间 R] [拓扑空间 V] [拓扑空间 W]
  证明: by
  simp_rw [coe_lineMap_eq, apply_lineMap]

Depends on / 依赖: apply_lineMap, coe_lineMap_eq, simp_rw
-/
theorem apply_lineMap' [TopologicalSpace R] [TopologicalSpace V] [TopologicalSpace W]
    [ContinuousSMul R V] [ContinuousSMul R W] [ContinuousVAdd V P] [ContinuousVAdd W Q]
    (f : P ->ᴬ[R] Q) (p₀ p₁ : P) (c : R) :
    f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c := by
  simp_rw [coe_lineMap_eq, apply_lineMap]

section IsTopologicalAddTorsor

variable [TopologicalSpace V] [IsTopologicalAddTorsor P]
variable [TopologicalSpace W] [IsTopologicalAddTorsor Q]
variable [TopologicalSpace W₂] [IsTopologicalAddTorsor Q₂]

/--
Definition of `contLinear` / `contLinear` 的定义

English:
definition contLinear
  signature: (f : P ->ᴬ[R] Q)
  body: { f.linear with
    toFun := f.linear
    cont := by rw [AffineMap.continuous_linear_iff]; exact f.cont }

@[simp]

中文:
定义 contLinear
  签名: (f : P ->ᴬ[R] Q)
  定义体: { f.linear with
    toFun := f.linear
    cont := by rw [AffineMap.continuous_linear_iff]; exact f.cont }

@[simp]

Depends on / 依赖: AffineMap, AffineMap.continuous_linear_iff, continuous_linear_iff, f.cont, f.linear, linear
-/
def contLinear (f : P ->ᴬ[R] Q) : V ->L[R] W :=
  { f.linear with
    toFun := f.linear
    cont := by rw [AffineMap.continuous_linear_iff]; exact f.cont }

@[simp]
/--
theorem `coe_contLinear` / 定理 `coe_contLinear`

English:
theorem coe_contLinear
  given: (f : P ->ᴬ[R] Q)
  statement: (f.contLinear : V -> W) = f.linear
  proof: rfl

@[simp]

中文:
定理 coe_contLinear
  条件: (f : P ->ᴬ[R] Q)
  结论: (f.contLinear : V -> W) = f.linear
  证明: rfl

@[simp]
-/
theorem coe_contLinear (f : P ->ᴬ[R] Q) : (f.contLinear : V -> W) = f.linear :=
  rfl

@[simp]
/--
theorem `coe_contLinear_eq_linear` / 定理 `coe_contLinear_eq_linear`

English:
theorem coe_contLinear_eq_linear
  given: (f : P ->ᴬ[R] Q)
  proof: rfl

@[simp]

中文:
定理 coe_contLinear_eq_linear
  条件: (f : P ->ᴬ[R] Q)
  证明: rfl

@[simp]
-/
theorem coe_contLinear_eq_linear (f : P ->ᴬ[R] Q) :
    (f.contLinear : V ->ₗ[R] W) = (f : P ->ᵃ[R] Q).linear :=
  rfl

@[simp]
/--
theorem `coe_mk_contLinear_eq_linear` / 定理 `coe_mk_contLinear_eq_linear`

English:
theorem coe_mk_contLinear_eq_linear
  given: (f : P ->ᵃ[R] Q) (h)
  proof: rfl

中文:
定理 coe_mk_contLinear_eq_linear
  条件: (f : P ->ᵃ[R] Q) (h)
  证明: rfl
-/
theorem coe_mk_contLinear_eq_linear (f : P ->ᵃ[R] Q) (h) :
    ((⟨f, h⟩ : P ->ᴬ[R] Q).contLinear : V -> W) = f.linear :=
  rfl

/--
theorem `coe_linear_eq_coe_contLinear` / 定理 `coe_linear_eq_coe_contLinear`

English:
theorem coe_linear_eq_coe_contLinear
  given: (f : P ->ᴬ[R] Q)
  proof: rfl

@[simp]

中文:
定理 coe_linear_eq_coe_contLinear
  条件: (f : P ->ᴬ[R] Q)
  证明: rfl

@[simp]
-/
theorem coe_linear_eq_coe_contLinear (f : P ->ᴬ[R] Q) :
    ((f : P ->ᵃ[R] Q).linear : V -> W) = (⇑f.contLinear : V -> W) :=
  rfl

@[simp]
/--
theorem `comp_contLinear` / 定理 `comp_contLinear`

English:
theorem comp_contLinear
  given: (f : P ->ᴬ[R] Q) (g : Q ->ᴬ[R] Q₂)
  proof: rfl

@[simp]

中文:
定理 comp_contLinear
  条件: (f : P ->ᴬ[R] Q) (g : Q ->ᴬ[R] Q₂)
  证明: rfl

@[simp]
-/
theorem comp_contLinear (f : P ->ᴬ[R] Q) (g : Q ->ᴬ[R] Q₂) :
    (g.comp f).contLinear = g.contLinear.comp f.contLinear :=
  rfl

@[simp]
/--
theorem `map_vadd` / 定理 `map_vadd`

English:
theorem map_vadd
  given: (f : P ->ᴬ[R] Q) (p : P) (v : V)
  statement: f (v +ᵥ p) = f.contLinear v +ᵥ f p
  proof: f.map_vadd' p v

@[simp]

中文:
定理 map_vadd
  条件: (f : P ->ᴬ[R] Q) (p : P) (v : V)
  结论: f (v +ᵥ p) = f.contLinear v +ᵥ f p
  证明: f.map_vadd' p v

@[simp]

Depends on / 依赖: f.map_vadd, map_vadd
-/
theorem map_vadd (f : P ->ᴬ[R] Q) (p : P) (v : V) : f (v +ᵥ p) = f.contLinear v +ᵥ f p :=
  f.map_vadd' p v

@[simp]
/--
theorem `contLinear_map_vsub` / 定理 `contLinear_map_vsub`

English:
theorem contLinear_map_vsub
  given: (f : P ->ᴬ[R] Q) (p₁ p₂ : P)
  statement: f.contLinear (p₁ -ᵥ p₂) = f p₁ -ᵥ f p₂
  proof: f.toAffineMap.linearMap_vsub p₁ p₂

@[simp]

中文:
定理 contLinear_map_vsub
  条件: (f : P ->ᴬ[R] Q) (p₁ p₂ : P)
  结论: f.contLinear (p₁ -ᵥ p₂) = f p₁ -ᵥ f p₂
  证明: f.toAffineMap.linearMap_vsub p₁ p₂

@[simp]

Depends on / 依赖: f.toAffineMap.linearMap_vsub, linearMap_vsub, toAffineMap
-/
theorem contLinear_map_vsub (f : P ->ᴬ[R] Q) (p₁ p₂ : P) : f.contLinear (p₁ -ᵥ p₂) = f p₁ -ᵥ f p₂ :=
  f.toAffineMap.linearMap_vsub p₁ p₂

@[simp]
/--
theorem `const_contLinear` / 定理 `const_contLinear`

English:
theorem const_contLinear
  given: (q : Q)
  statement: (const R P q).contLinear = 0
  proof: rfl

中文:
定理 const_contLinear
  条件: (q : Q)
  结论: (const R P q).contLinear = 0
  证明: rfl

Depends on / 依赖: DiscreteUniformity, DiscreteUniformity.mk
-/
theorem const_contLinear (q : Q) : (const R P q).contLinear = 0 :=
  rfl

/--
theorem `contLinear_eq_zero_iff_exists_const` / 定理 `contLinear_eq_zero_iff_exists_const`

English:
theorem contLinear_eq_zero_iff_exists_const
  given: (f : P ->ᴬ[R] Q)
  proof: by
  have h₁ : f.contLinear = 0 ↔ (f : P ->ᵃ[R] Q).linear = 0 := by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> ext
    · rw [← coe_contLinear_eq_linear, h]; rfl
    · rw [← coe_linear_eq_coe_contLinear, h]; rfl
  have h₂ : forall q : Q, f = const R P q ↔ (f : P ->ᵃ[R] Q) = AffineMap.const R P q := by

中文:
定理 contLinear_eq_zero_iff_存在_const
  条件: (f : P ->ᴬ[R] Q)
  证明: by
  have h₁ : f.contLinear = 0 ↔ (f : P ->ᵃ[R] Q).linear = 0 := by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> ext
    · rw [← coe_contLinear_eq_linear, h]; rfl
    · rw [← coe_linear_eq_coe_contLinear, h]; rfl
  have h₂ : forall q : Q, f = const R P q ↔ (f : P ->ᵃ[R] Q) = AffineMap.const R P q := by

Depends on / 依赖: AffineMap, AffineMap.const, AffineMap.const_apply, Function, Function.const_apply, coe_const, coe_contLinear_eq_linear, coe_linear_eq_coe_contLinear, coe_toAffineMap, const_apply, contLinear, f.contLinear, linear, linear_eq_zero_iff_exists_c, simp_rw
-/
theorem contLinear_eq_zero_iff_exists_const (f : P ->ᴬ[R] Q) :
    f.contLinear = 0 ↔ exists q, f = const R P q := by
  have h₁ : f.contLinear = 0 ↔ (f : P ->ᵃ[R] Q).linear = 0 := by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> ext
    · rw [← coe_contLinear_eq_linear, h]; rfl
    · rw [← coe_linear_eq_coe_contLinear, h]; rfl
  have h₂ : forall q : Q, f = const R P q ↔ (f : P ->ᵃ[R] Q) = AffineMap.const R P q := by
    intro q
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> ext
    · rw [h]; rfl
    · rw [← coe_toAffineMap, h, AffineMap.const_apply, coe_const, Function.const_apply]
  simp_rw [h₁, h₂]
  exact (f : P ->ᵃ[R] Q).linear_eq_zero_iff_exists_const

end IsTopologicalAddTorsor

section ModuleValuedMaps

variable {S : Type*}
variable [TopologicalSpace W]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (P ->ᴬ[R] W)
  body: ⟨ContinuousAffineMap.const R P 0⟩

@[norm_cast, simp]

中文:
实例 :
  签名: 零 (P ->ᴬ[R] W)
  定义体: ⟨ContinuousAffineMap.const R P 0⟩

@[norm_cast, simp]

Depends on / 依赖: ContinuousAffineMap, ContinuousAffineMap.const
-/
instance : Zero (P ->ᴬ[R] W) :=
  ⟨ContinuousAffineMap.const R P 0⟩

@[norm_cast, simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : P ->ᴬ[R] W) : P -> W) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: ((0 : P ->ᴬ[R] W) : P -> W) = 0
  证明: rfl
-/
theorem coe_zero : ((0 : P ->ᴬ[R] W) : P -> W) = 0 := rfl

/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (x : P)
  statement: (0 : P ->ᴬ[R] W) x = 0
  proof: rfl

中文:
定理 zero_apply
  条件: (x : P)
  结论: (0 : P ->ᴬ[R] W) x = 0
  证明: rfl
-/
theorem zero_apply (x : P) : (0 : P ->ᴬ[R] W) x = 0 := rfl

section MulAction

variable [Monoid S] [DistribMulAction S W] [SMulCommClass R S W]
variable [ContinuousConstSMul S W]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul S (P ->ᴬ[R] W)
  body: { t • (f : P ->ᵃ[R] W) with cont := f.continuous.const_smul t }

@[norm_cast, simp]

中文:
实例 :
  签名: 标量乘法 S (P ->ᴬ[R] W)
  定义体: { t • (f : P ->ᵃ[R] W) with cont := f.continuous.const_smul t }

@[norm_cast, simp]

Depends on / 依赖: const_smul, continuous, f.continuous.const_smul
-/
instance : SMul S (P ->ᴬ[R] W) where
  smul t f := { t • (f : P ->ᵃ[R] W) with cont := f.continuous.const_smul t }

@[norm_cast, simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (t : S) (f : P ->ᴬ[R] W)
  statement: ⇑(t • f) = t • ⇑f
  proof: rfl

中文:
定理 coe_smul
  条件: (t : S) (f : P ->ᴬ[R] W)
  结论: ⇑(t • f) = t • ⇑f
  证明: rfl

Depends on / 依赖: Filter, Filter.iInter_mem, Filter.mem_pure, Set.mem_singleton_iff, SetRel, SetRel.id, discreteUniformity_iff_setRelId_mem_uniformity, iInter_mem, implies_true, mem_nhds_uniformity_iff_left, mem_pure, mem_singleton_iff, nhds_discrete, simp_rw
-/
theorem coe_smul (t : S) (f : P ->ᴬ[R] W) : ⇑(t • f) = t • ⇑f := rfl

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (t : S) (f : P ->ᴬ[R] W) (x : P)
  statement: (t • f) x = t • f x
  proof: rfl

中文:
定理 smul_apply
  条件: (t : S) (f : P ->ᴬ[R] W) (x : P)
  结论: (t • f) x = t • f x
  证明: rfl

Depends on / 依赖: Prod.ext_iff, Set.ofPred_and, Set.prod_eq, SetRel, SetRel.id, discreteUniformity_iff_eq_principal_setRelId, eq_principal_setRelId, ext_iff, ofPred_and, prod_eq, uniformity_prod_eq_comap_prod
-/
theorem smul_apply (t : S) (f : P ->ᴬ[R] W) (x : P) : (t • f) x = t • f x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribMulAction
  signature: Sᵐᵒᵖ W] [IsCentralScalar S W] : IsCentralScalar S (P ->ᴬ[R] W) where
  body: ext fun _ => op_smul_eq_smul _ _

中文:
实例 [分配乘法作用
  签名: Sᵐᵒᵖ W] [中心标量 S W] : 中心标量 S (P ->ᴬ[R] W) where
  定义体: ext fun _ => op_smul_eq_smul _ _

Depends on / 依赖: op_smul_eq_smul
-/
instance [DistribMulAction Sᵐᵒᵖ W] [IsCentralScalar S W] : IsCentralScalar S (P ->ᴬ[R] W) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction S (P ->ᴬ[R] W)
  body: Function.Injective.mulAction _ coe_injective coe_smul

中文:
实例 :
  签名: 乘法作用 S (P ->ᴬ[R] W)
  定义体: Function.Injective.mulAction _ coe_injective coe_smul

Depends on / 依赖: Function, Function.Injective.mulAction, Injective, coe_injective, coe_smul, mulAction
-/
instance : MulAction S (P ->ᴬ[R] W) :=
  Function.Injective.mulAction _ coe_injective coe_smul

variable [TopologicalSpace V] [IsTopologicalAddTorsor P] [IsTopologicalAddGroup W]

@[simp]
/--
theorem `smul_contLinear` / 定理 `smul_contLinear`

English:
theorem smul_contLinear
  given: (t : S) (f : P ->ᴬ[R] W)
  statement: (t • f).contLinear = t • f.contLinear
  proof: rfl

中文:
定理 smul_contLinear
  条件: (t : S) (f : P ->ᴬ[R] W)
  结论: (t • f).contLinear = t • f.contLinear
  证明: rfl
-/
theorem smul_contLinear (t : S) (f : P ->ᴬ[R] W) : (t • f).contLinear = t • f.contLinear :=
  rfl

end MulAction

variable [IsTopologicalAddGroup W]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (P ->ᴬ[R] W)
  body: { (f : P ->ᵃ[R] W) + (g : P ->ᵃ[R] W) with cont := f.continuous.add g.continuous }

@[norm_cast, simp]

中文:
实例 :
  签名: 加法 (P ->ᴬ[R] W)
  定义体: { (f : P ->ᵃ[R] W) + (g : P ->ᵃ[R] W) with cont := f.continuous.add g.continuous }

@[norm_cast, simp]

Depends on / 依赖: continuous, f.continuous.add, g.continuous
-/
instance : Add (P ->ᴬ[R] W) where
  add f g := { (f : P ->ᵃ[R] W) + (g : P ->ᵃ[R] W) with cont := f.continuous.add g.continuous }

@[norm_cast, simp]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (f g : P ->ᴬ[R] W)
  statement: ⇑(f + g) = f + g
  proof: rfl

中文:
定理 coe_add
  条件: (f g : P ->ᴬ[R] W)
  结论: ⇑(f + g) = f + g
  证明: rfl
-/
theorem coe_add (f g : P ->ᴬ[R] W) : ⇑(f + g) = f + g := rfl

/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: (f g : P ->ᴬ[R] W) (x : P)
  statement: (f + g) x = f x + g x
  proof: rfl

中文:
定理 add_apply
  条件: (f g : P ->ᴬ[R] W) (x : P)
  结论: (f + g) x = f x + g x
  证明: rfl
-/
theorem add_apply (f g : P ->ᴬ[R] W) (x : P) : (f + g) x = f x + g x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (P ->ᴬ[R] W)
  body: { (f : P ->ᵃ[R] W) - (g : P ->ᵃ[R] W) with cont := f.continuous.sub g.continuous }

@[norm_cast, simp]

中文:
实例 :
  签名: 减法 (P ->ᴬ[R] W)
  定义体: { (f : P ->ᵃ[R] W) - (g : P ->ᵃ[R] W) with cont := f.continuous.sub g.continuous }

@[norm_cast, simp]

Depends on / 依赖: continuous, f.continuous.sub, g.continuous
-/
instance : Sub (P ->ᴬ[R] W) where
  sub f g := { (f : P ->ᵃ[R] W) - (g : P ->ᵃ[R] W) with cont := f.continuous.sub g.continuous }

@[norm_cast, simp]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (f g : P ->ᴬ[R] W)
  statement: ⇑(f - g) = f - g
  proof: rfl

中文:
定理 coe_sub
  条件: (f g : P ->ᴬ[R] W)
  结论: ⇑(f - g) = f - g
  证明: rfl
-/
theorem coe_sub (f g : P ->ᴬ[R] W) : ⇑(f - g) = f - g := rfl

/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: (f g : P ->ᴬ[R] W) (x : P)
  statement: (f - g) x = f x - g x
  proof: rfl

中文:
定理 sub_apply
  条件: (f g : P ->ᴬ[R] W) (x : P)
  结论: (f - g) x = f x - g x
  证明: rfl
-/
theorem sub_apply (f g : P ->ᴬ[R] W) (x : P) : (f - g) x = f x - g x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (P ->ᴬ[R] W)
  body: { neg := fun f => { -(f : P ->ᵃ[R] W) with cont := f.continuous.neg } }

@[norm_cast, simp]

中文:
实例 :
  签名: 取负 (P ->ᴬ[R] W)
  定义体: { neg := fun f => { -(f : P ->ᵃ[R] W) with cont := f.continuous.neg } }

@[norm_cast, simp]

Depends on / 依赖: continuous, f.continuous.neg
-/
instance : Neg (P ->ᴬ[R] W) :=
  { neg := fun f => { -(f : P ->ᵃ[R] W) with cont := f.continuous.neg } }

@[norm_cast, simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (f : P ->ᴬ[R] W)
  statement: ⇑(-f) = -f
  proof: rfl

中文:
定理 coe_neg
  条件: (f : P ->ᴬ[R] W)
  结论: ⇑(-f) = -f
  证明: rfl
-/
theorem coe_neg (f : P ->ᴬ[R] W) : ⇑(-f) = -f := rfl

/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: (f : P ->ᴬ[R] W) (x : P)
  statement: (-f) x = -f x
  proof: rfl

中文:
定理 neg_apply
  条件: (f : P ->ᴬ[R] W) (x : P)
  结论: (-f) x = -f x
  证明: rfl
-/
theorem neg_apply (f : P ->ᴬ[R] W) (x : P) : (-f) x = -f x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (P ->ᴬ[R] W)
  body: coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _) fun _ _ =>
    coe_smul _ _

中文:
实例 :
  签名: 加法交换群 (P ->ᴬ[R] W)
  定义体: coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _) fun _ _ =>
    coe_smul _ _

Depends on / 依赖: addCommGroup, coe_add, coe_injective, coe_injective.addCommGroup, coe_neg, coe_smul, coe_sub, coe_zero
-/
instance : AddCommGroup (P ->ᴬ[R] W) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _) fun _ _ =>
    coe_smul _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: S] [DistribMulAction S W] [SMulCommClass R S W] [ContinuousConstSMul S W] :
  body: Function.Injective.distribMulAction ⟨⟨fun f => f.toAffineMap.toFun, rfl⟩, coe_add⟩ coe_injective
    coe_smul

中文:
实例 [幺半群
  签名: S] [分配乘法作用 S W] [标量交换类 R S W] [连续常数标量乘法 S W] :
  定义体: Function.Injective.distribMulAction ⟨⟨fun f => f.toAffineMap.toFun, rfl⟩, coe_add⟩ coe_injective
    coe_smul

Depends on / 依赖: Function, Function.Injective.distribMulAction, Injective, coe_add, coe_injective, coe_smul, distribMulAction, f.toAffineMap.toFun, toAffineMap
-/
instance [Monoid S] [DistribMulAction S W] [SMulCommClass R S W] [ContinuousConstSMul S W] :
    DistribMulAction S (P ->ᴬ[R] W) :=
  Function.Injective.distribMulAction ⟨⟨fun f => f.toAffineMap.toFun, rfl⟩, coe_add⟩ coe_injective
    coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: S] [Module S W] [SMulCommClass R S W] [ContinuousConstSMul S W] :
  body: Function.Injective.module S ⟨⟨fun f => f.toAffineMap.toFun, rfl⟩, coe_add⟩ coe_injective coe_smul

中文:
实例 [半环
  签名: S] [模 S W] [标量交换类 R S W] [连续常数标量乘法 S W] :
  定义体: Function.Injective.module S ⟨⟨fun f => f.toAffineMap.toFun, rfl⟩, coe_add⟩ coe_injective coe_smul

Depends on / 依赖: Function, Function.Injective.module, Injective, coe_add, coe_injective, coe_smul, f.toAffineMap.toFun, module, toAffineMap
-/
instance [Semiring S] [Module S W] [SMulCommClass R S W] [ContinuousConstSMul S W] :
    Module S (P ->ᴬ[R] W) :=
  Function.Injective.module S ⟨⟨fun f => f.toAffineMap.toFun, rfl⟩, coe_add⟩ coe_injective coe_smul

variable [TopologicalSpace V] [IsTopologicalAddTorsor P]

@[simp]
/--
theorem `zero_contLinear` / 定理 `zero_contLinear`

English:
theorem zero_contLinear
  statement: (0 : P ->ᴬ[R] W).contLinear = 0
  proof: rfl

@[simp]

中文:
定理 zero_contLinear
  结论: (0 : P ->ᴬ[R] W).contLinear = 0
  证明: rfl

@[simp]
-/
theorem zero_contLinear : (0 : P ->ᴬ[R] W).contLinear = 0 :=
  rfl

@[simp]
/--
theorem `add_contLinear` / 定理 `add_contLinear`

English:
theorem add_contLinear
  given: (f g : P ->ᴬ[R] W)
  statement: (f + g).contLinear = f.contLinear + g.contLinear
  proof: rfl

@[simp]

中文:
定理 add_contLinear
  条件: (f g : P ->ᴬ[R] W)
  结论: (f + g).contLinear = f.contLinear + g.contLinear
  证明: rfl

@[simp]
-/
theorem add_contLinear (f g : P ->ᴬ[R] W) : (f + g).contLinear = f.contLinear + g.contLinear :=
  rfl

@[simp]
/--
theorem `sub_contLinear` / 定理 `sub_contLinear`

English:
theorem sub_contLinear
  given: (f g : P ->ᴬ[R] W)
  statement: (f - g).contLinear = f.contLinear - g.contLinear
  proof: rfl

@[simp]

中文:
定理 sub_contLinear
  条件: (f g : P ->ᴬ[R] W)
  结论: (f - g).contLinear = f.contLinear - g.contLinear
  证明: rfl

@[simp]
-/
theorem sub_contLinear (f g : P ->ᴬ[R] W) : (f - g).contLinear = f.contLinear - g.contLinear :=
  rfl

@[simp]
/--
theorem `neg_contLinear` / 定理 `neg_contLinear`

English:
theorem neg_contLinear
  given: (f : P ->ᴬ[R] W)
  statement: (-f).contLinear = -f.contLinear
  proof: rfl

中文:
定理 neg_contLinear
  条件: (f : P ->ᴬ[R] W)
  结论: (-f).contLinear = -f.contLinear
  证明: rfl
-/
theorem neg_contLinear (f : P ->ᴬ[R] W) : (-f).contLinear = -f.contLinear :=
  rfl

end ModuleValuedMaps

section

variable [TopologicalSpace W] [IsTopologicalAddGroup W] [IsTopologicalAddTorsor Q]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddTorsor (P ->ᴬ[R] W) (P ->ᴬ[R] Q)
  body: { __ := f.toAffineMap +ᵥ g.toAffineMap, cont := f.cont.vadd g.cont }
  zero_vadd _ := ext fun _ => zero_vadd _ _
  add_vadd _ _ _ := ext fun _ => add_vadd _ _ _
  vsub f g := { __ := f.toAffineMap -ᵥ g.toAffineMap, cont := f.cont.vsub g.cont }
  vsub_vadd' _ _ := ext fun _ => vsub_vadd _ _
  vadd_vs

中文:
实例 :
  签名: 加法Torsor (P ->ᴬ[R] W) (P ->ᴬ[R] Q)
  定义体: { __ := f.toAffineMap +ᵥ g.toAffineMap, cont := f.cont.vadd g.cont }
  zero_vadd _ := ext fun _ => zero_vadd _ _
  add_vadd _ _ _ := ext fun _ => add_vadd _ _ _
  vsub f g := { __ := f.toAffineMap -ᵥ g.toAffineMap, cont := f.cont.vsub g.cont }
  vsub_vadd' _ _ := ext fun _ => vsub_vadd _ _
  vadd_vs

Depends on / 依赖: f.cont.vadd, f.toAffineMap, g.cont, g.toAffineMap, toAffineMap
-/
instance : AddTorsor (P ->ᴬ[R] W) (P ->ᴬ[R] Q) where
  vadd f g := { __ := f.toAffineMap +ᵥ g.toAffineMap, cont := f.cont.vadd g.cont }
  zero_vadd _ := ext fun _ => zero_vadd _ _
  add_vadd _ _ _ := ext fun _ => add_vadd _ _ _
  vsub f g := { __ := f.toAffineMap -ᵥ g.toAffineMap, cont := f.cont.vsub g.cont }
  vsub_vadd' _ _ := ext fun _ => vsub_vadd _ _
  vadd_vsub' _ _ := ext fun _ => vadd_vsub _ _

/--
lemma `vadd_apply` / 引理 `vadd_apply`

English:
lemma vadd_apply
  given: (f : P ->ᴬ[R] W) (g : P ->ᴬ[R] Q) (p : P)
  statement: (f +ᵥ g) p = f p +ᵥ g p
  proof: rfl

中文:
引理 vadd_apply
  条件: (f : P ->ᴬ[R] W) (g : P ->ᴬ[R] Q) (p : P)
  结论: (f +ᵥ g) p = f p +ᵥ g p
  证明: rfl
-/
@[simp] lemma vadd_apply (f : P ->ᴬ[R] W) (g : P ->ᴬ[R] Q) (p : P) : (f +ᵥ g) p = f p +ᵥ g p :=
  rfl

/--
lemma `vsub_apply` / 引理 `vsub_apply`

English:
lemma vsub_apply
  given: (f g : P ->ᴬ[R] Q) (p : P)
  statement: (f -ᵥ g) p = f p -ᵥ g p
  proof: rfl

中文:
引理 vsub_apply
  条件: (f g : P ->ᴬ[R] Q) (p : P)
  结论: (f -ᵥ g) p = f p -ᵥ g p
  证明: rfl
-/
@[simp] lemma vsub_apply (f g : P ->ᴬ[R] Q) (p : P) : (f -ᵥ g) p = f p -ᵥ g p :=
  rfl

/--
lemma `vadd_toAffineMap` / 引理 `vadd_toAffineMap`

English:
lemma vadd_toAffineMap
  given: (f : P ->ᴬ[R] W) (g : P ->ᴬ[R] Q)
  proof: rfl

中文:
引理 vadd_toAffineMap
  条件: (f : P ->ᴬ[R] W) (g : P ->ᴬ[R] Q)
  证明: rfl
-/
@[simp] lemma vadd_toAffineMap (f : P ->ᴬ[R] W) (g : P ->ᴬ[R] Q) :
    (f +ᵥ g).toAffineMap = f.toAffineMap +ᵥ g.toAffineMap :=
  rfl

/--
lemma `vsub_toAffineMap` / 引理 `vsub_toAffineMap`

English:
lemma vsub_toAffineMap
  given: (f g : P ->ᴬ[R] Q)
  proof: rfl

中文:
引理 vsub_toAffineMap
  条件: (f g : P ->ᴬ[R] Q)
  证明: rfl
-/
@[simp] lemma vsub_toAffineMap (f g : P ->ᴬ[R] Q) :
    (f -ᵥ g).toAffineMap = f.toAffineMap -ᵥ g.toAffineMap :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Interpolating between `ContinuousAffineMap`s with `AffineMap.lineMap` commutes with
evaluation. -/
@[simp]
/--
lemma `lineMap_apply'` / 引理 `lineMap_apply'`

English:
lemma lineMap_apply'
  statement: [ContinuousConstSMul R W] [SMulCommClass R R W] (f g : P ->ᴬ[R] Q) (c : R)
  proof: by
  simp [AffineMap.lineMap_apply]

中文:
引理 lineMap_apply'
  结论: [连续常数标量乘法 R W] [标量交换类 R R W] (f g : P ->ᴬ[R] Q) (c : R)
  证明: by
  simp [AffineMap.lineMap_apply]

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply, lineMap_apply
-/
lemma lineMap_apply' [ContinuousConstSMul R W] [SMulCommClass R R W] (f g : P ->ᴬ[R] Q) (c : R)
    (p : P) : AffineMap.lineMap f g c p = AffineMap.lineMap (f p) (g p) c := by
  simp [AffineMap.lineMap_apply]

variable [TopologicalSpace V] [IsTopologicalAddTorsor P]

/--
lemma `vadd_contLinear` / 引理 `vadd_contLinear`

English:
lemma vadd_contLinear
  given: (f : P ->ᴬ[R] W) (g : P ->ᴬ[R] Q)
  proof: rfl

中文:
引理 vadd_contLinear
  条件: (f : P ->ᴬ[R] W) (g : P ->ᴬ[R] Q)
  证明: rfl
-/
@[simp] lemma vadd_contLinear (f : P ->ᴬ[R] W) (g : P ->ᴬ[R] Q) :
    (f +ᵥ g).contLinear = f.contLinear + g.contLinear :=
  rfl

/--
lemma `vsub_contLinear` / 引理 `vsub_contLinear`

English:
lemma vsub_contLinear
  given: (f g : P ->ᴬ[R] Q)
  proof: rfl

中文:
引理 vsub_contLinear
  条件: (f g : P ->ᴬ[R] Q)
  证明: rfl
-/
@[simp] lemma vsub_contLinear (f g : P ->ᴬ[R] Q) :
    (f -ᵥ g).contLinear = f.contLinear - g.contLinear :=
  rfl

end

section Prod

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂]
  [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃] [TopologicalSpace P₃]
  [AddCommGroup V₄] [Module k V₄] [AddTorsor V₄ P₄] [TopologicalSpace P₄]

/-- The product of two continuous affine maps is a continuous affine map. -/
@[simps toAffineMap]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃)
  body: AffineMap.prod f g
  cont := by eta_expand; dsimp; fun_prop

中文:
定义 乘积
  签名: (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃)
  定义体: AffineMap.prod f g
  cont := by eta_expand; dsimp; fun_prop

Depends on / 依赖: AffineMap, AffineMap.prod
-/
def prod (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃) : P₁ ->ᴬ[k] P₂ × P₃ where
  __ := AffineMap.prod f g
  cont := by eta_expand; dsimp; fun_prop

/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃)
  statement: prod f g = Function.prod f g
  proof: rfl

@[simp]

中文:
定理 coe_prod
  条件: (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃)
  结论: 乘积 f g = 函数.乘积 f g
  证明: rfl

@[simp]
-/
theorem coe_prod (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃) : prod f g = Function.prod f g :=
  rfl

@[simp]
/--
theorem `prod_apply` / 定理 `prod_apply`

English:
theorem prod_apply
  given: (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃) (p : P₁)
  statement: prod f g p = (f p, g p)
  proof: rfl

中文:
定理 prod_apply
  条件: (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃) (p : P₁)
  结论: 乘积 f g p = (f p, g p)
  证明: rfl
-/
theorem prod_apply (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃) (p : P₁) : prod f g p = (f p, g p) :=
  rfl

/-- `Prod.map` of two continuous affine maps. -/
@[simps toAffineMap]
/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄)
  body: AffineMap.prodMap f g
  cont := by eta_expand; dsimp; fun_prop

中文:
定义 prodMap
  签名: (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄)
  定义体: AffineMap.prodMap f g
  cont := by eta_expand; dsimp; fun_prop

Depends on / 依赖: AffineMap, AffineMap.prodMap, prodMap
-/
def prodMap (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄) : P₁ × P₃ ->ᴬ[k] P₂ × P₄ where
  __ := AffineMap.prodMap f g
  cont := by eta_expand; dsimp; fun_prop

/--
theorem `coe_prodMap` / 定理 `coe_prodMap`

English:
theorem coe_prodMap
  given: (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄)
  statement: ⇑(f.prodMap g) = Prod.map f g
  proof: rfl

@[simp]

中文:
定理 coe_prodMap
  条件: (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄)
  结论: ⇑(f.prodMap g) = 积类型.map f g
  证明: rfl

@[simp]
-/
theorem coe_prodMap (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄) : ⇑(f.prodMap g) = Prod.map f g :=
  rfl

@[simp]
/--
theorem `prodMap_apply` / 定理 `prodMap_apply`

English:
theorem prodMap_apply
  given: (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄) (x)
  statement: f.prodMap g x = (f x.1, g x.2)
  proof: rfl

中文:
定理 prodMap_apply
  条件: (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄) (x)
  结论: f.prodMap g x = (f x.1, g x.2)
  证明: rfl
-/
theorem prodMap_apply (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄) (x) : f.prodMap g x = (f x.1, g x.2) :=
  rfl

variable
  [TopologicalSpace V₁] [IsTopologicalAddTorsor P₁]
  [TopologicalSpace V₂] [IsTopologicalAddTorsor P₂]
  [TopologicalSpace V₃] [IsTopologicalAddTorsor P₃]
  [TopologicalSpace V₄] [IsTopologicalAddTorsor P₄]

@[simp]
/--
theorem `prod_contLinear` / 定理 `prod_contLinear`

English:
theorem prod_contLinear
  given: (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃)
  proof: rfl

@[simp]

中文:
定理 prod_contLinear
  条件: (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃)
  证明: rfl

@[simp]
-/
theorem prod_contLinear (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃) :
    (f.prod g).contLinear = f.contLinear.prod g.contLinear :=
  rfl

@[simp]
/--
theorem `prodMap_contLinear` / 定理 `prodMap_contLinear`

English:
theorem prodMap_contLinear
  given: (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄)
  proof: rfl

中文:
定理 prodMap_contLinear
  条件: (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄)
  证明: rfl
-/
theorem prodMap_contLinear (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄) :
    (f.prodMap g).contLinear = f.contLinear.prodMap g.contLinear :=
  rfl

end Prod

end ContinuousAffineMap

namespace ContinuousLinearMap

variable {R V W : Type*} [Ring R]
variable [AddCommGroup V] [Module R V] [TopologicalSpace V]
variable [AddCommGroup W] [Module R W] [TopologicalSpace W]

/--
Definition of `toContinuousAffineMap` / `toContinuousAffineMap` 的定义

English:
definition toContinuousAffineMap
  signature: (f : V ->L[R] W)
  body: f
  linear := f
  map_vadd' := by simp
  cont := f.cont

@[simp]

中文:
定义 toContinuousAffineMap
  签名: (f : V ->L[R] W)
  定义体: f
  linear := f
  map_vadd' := by simp
  cont := f.cont

@[simp]
-/
def toContinuousAffineMap (f : V ->L[R] W) : V ->ᴬ[R] W where
  toFun := f
  linear := f
  map_vadd' := by simp
  cont := f.cont

@[simp]
/--
theorem `coe_toContinuousAffineMap` / 定理 `coe_toContinuousAffineMap`

English:
theorem coe_toContinuousAffineMap
  given: (f : V ->L[R] W)
  statement: ⇑f.toContinuousAffineMap = f
  proof: rfl

@[simp]

中文:
定理 coe_toContinuousAffineMap
  条件: (f : V ->L[R] W)
  结论: ⇑f.toContinuousAffineMap = f
  证明: rfl

@[simp]
-/
theorem coe_toContinuousAffineMap (f : V ->L[R] W) : ⇑f.toContinuousAffineMap = f := rfl

@[simp]
/--
theorem `toContinuousAffineMap_map_zero` / 定理 `toContinuousAffineMap_map_zero`

English:
theorem toContinuousAffineMap_map_zero
  given: (f : V ->L[R] W)
  statement: f.toContinuousAffineMap 0 = 0
  proof: by simp

中文:
定理 toContinuousAffineMap_map_zero
  条件: (f : V ->L[R] W)
  结论: f.toContinuousAffineMap 0 = 0
  证明: by simp
-/
theorem toContinuousAffineMap_map_zero (f : V ->L[R] W) : f.toContinuousAffineMap 0 = 0 := by simp

variable [IsTopologicalAddGroup V] [IsTopologicalAddGroup W]

@[simp]
/--
theorem `toContinuousAffineMap_contLinear` / 定理 `toContinuousAffineMap_contLinear`

English:
theorem toContinuousAffineMap_contLinear
  given: (f : V ->L[R] W)
  statement: f.toContinuousAffineMap.contLinear = f
  proof: rfl

中文:
定理 toContinuousAffineMap_contLinear
  条件: (f : V ->L[R] W)
  结论: f.toContinuousAffineMap.contLinear = f
  证明: rfl
-/
theorem toContinuousAffineMap_contLinear (f : V ->L[R] W) : f.toContinuousAffineMap.contLinear = f :=
  rfl

/--
theorem `_root_.ContinuousAffineMap.decomp` / 定理 `_root_.ContinuousAffineMap.decomp`

English:
theorem _root_.ContinuousAffineMap.decomp
  given: (f : V ->ᴬ[R] W)
  proof: by
  rcases f with ⟨f, h⟩
  rw [ContinuousAffineMap.coe_mk_contLinear_eq_linear]; rw [ContinuousAffineMap.coe_mk]; rw [f.decomp]; rw [Pi.add_apply]; rw [LinearMap.map_zero]; rw [zero_add]; rw [← Function.const_def]

中文:
定理 _root_.余ntinuousAffine映射.decomp
  条件: (f : V ->ᴬ[R] W)
  证明: by
  rcases f with ⟨f, h⟩
  rw [ContinuousAffineMap.coe_mk_contLinear_eq_linear]; rw [ContinuousAffineMap.coe_mk]; rw [f.decomp]; rw [Pi.add_apply]; rw [LinearMap.map_zero]; rw [zero_add]; rw [← Function.const_def]

Depends on / 依赖: ContinuousAffineMap, ContinuousAffineMap.coe_mk, ContinuousAffineMap.coe_mk_contLinear_eq_linear, Function, Function.const_def, LinearMap, LinearMap.map_zero, Pi.add_apply, add_apply, coe_mk, coe_mk_contLinear_eq_linear, const_def, decomp, f.decomp, map_zero, zero_add
-/
theorem _root_.ContinuousAffineMap.decomp (f : V ->ᴬ[R] W) :
    (f : V -> W) = f.contLinear + Function.const V (f 0) := by
  rcases f with ⟨f, h⟩
  rw [ContinuousAffineMap.coe_mk_contLinear_eq_linear]; rw [ContinuousAffineMap.coe_mk]; rw [f.decomp]; rw [Pi.add_apply]; rw [LinearMap.map_zero]; rw [zero_add]; rw [← Function.const_def]

end ContinuousLinearMap

namespace ContinuousAffineMap

variable (R S V : Type*) {W : Type*} (Q : Type*) [Ring S] [Ring R]
variable [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [AddCommGroup W] [Module R W] [TopologicalSpace W]
variable [Module S W] [SMulCommClass R S W] [ContinuousConstSMul S W]
variable [AddTorsor W Q] [TopologicalSpace Q]

section

variable [IsTopologicalAddTorsor Q]

/--
Definition of `decompEquiv` / `decompEquiv` 的定义

English:
definition decompEquiv
  signature: : (V ->ᴬ[R] Q) ≃ Q × (V ->L[R] W) where
  body: ⟨f 0, f.contLinear⟩
  invFun p :=
    haveI := IsTopologicalAddTorsor.to_isTopologicalAddGroup W Q
    p.2.toContinuousAffineMap +ᵥ const R V p.1
  left_inv f := by
    ext x
    simp_rw [vadd_apply, f.contLinear.coe_toContinuousAffineMap, coe_const, Function.const_apply,
      ← f.map_vadd, vadd_eq

中文:
定义 decompEquiv
  签名: : (V ->ᴬ[R] Q) ≃ Q × (V ->L[R] W) where
  定义体: ⟨f 0, f.contLinear⟩
  invFun p :=
    haveI := IsTopologicalAddTorsor.to_isTopologicalAddGroup W Q
    p.2.toContinuousAffineMap +ᵥ const R V p.1
  left_inv f := by
    ext x
    simp_rw [vadd_apply, f.contLinear.coe_toContinuousAffineMap, coe_const, Function.const_apply,
      ← f.map_vadd, vadd_eq

Depends on / 依赖: contLinear, f.contLinear
-/
def decompEquiv : (V ->ᴬ[R] Q) ≃ Q × (V ->L[R] W) where
  toFun f := ⟨f 0, f.contLinear⟩
  invFun p :=
    haveI := IsTopologicalAddTorsor.to_isTopologicalAddGroup W Q
    p.2.toContinuousAffineMap +ᵥ const R V p.1
  left_inv f := by
    ext x
    simp_rw [vadd_apply, f.contLinear.coe_toContinuousAffineMap, coe_const, Function.const_apply,
      ← f.map_vadd, vadd_eq_add, add_zero]
  right_inv := by
    have := IsTopologicalAddTorsor.to_isTopologicalAddGroup W Q
    rintro ⟨v, f⟩; ext <;> simp

@[simp]
/--
theorem `fst_decompEquiv` / 定理 `fst_decompEquiv`

English:
theorem fst_decompEquiv
  given: (f : V ->ᴬ[R] Q)
  proof: rfl

@[simp]

中文:
定理 fst_decompEquiv
  条件: (f : V ->ᴬ[R] Q)
  证明: rfl

@[simp]
-/
theorem fst_decompEquiv (f : V ->ᴬ[R] Q) :
    (decompEquiv R V Q f).1 = f 0 :=
  rfl

@[simp]
/--
theorem `snd_decompEquiv` / 定理 `snd_decompEquiv`

English:
theorem snd_decompEquiv
  given: (f : V ->ᴬ[R] Q)
  proof: rfl

@[simp]

中文:
定理 snd_decompEquiv
  条件: (f : V ->ᴬ[R] Q)
  证明: rfl

@[simp]
-/
theorem snd_decompEquiv (f : V ->ᴬ[R] Q) :
    (decompEquiv R V Q f).2 = f.contLinear :=
  rfl

@[simp]
/--
theorem `decompEquiv_symm_apply` / 定理 `decompEquiv_symm_apply`

English:
theorem decompEquiv_symm_apply
  given: (p : Q × (V ->L[R] W)) (x : V)
  proof: rfl

中文:
定理 decompEquiv_symm_apply
  条件: (p : Q × (V ->L[R] W)) (x : V)
  证明: rfl
-/
theorem decompEquiv_symm_apply (p : Q × (V ->L[R] W)) (x : V) :
    (decompEquiv R V Q).symm p x = p.2 x +ᵥ p.1 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `decompEquiv_symm_contLinear` / 定理 `decompEquiv_symm_contLinear`

English:
theorem decompEquiv_symm_contLinear
  given: (p : Q × (V ->L[R] W))
  proof: by
  have := IsTopologicalAddTorsor.to_isTopologicalAddGroup W Q
  ext; simp [decompEquiv]

中文:
定理 decompEquiv_symm_contLinear
  条件: (p : Q × (V ->L[R] W))
  证明: by
  have := IsTopologicalAddTorsor.to_isTopologicalAddGroup W Q
  ext; simp [decompEquiv]

Depends on / 依赖: IsTopologicalAddTorsor, IsTopologicalAddTorsor.to_isTopologicalAddGroup, decompEquiv, to_isTopologicalAddGroup
-/
theorem decompEquiv_symm_contLinear (p : Q × (V ->L[R] W)) :
    ((decompEquiv R V Q).symm p).contLinear = p.2 := by
  have := IsTopologicalAddTorsor.to_isTopologicalAddGroup W Q
  ext; simp [decompEquiv]

end

section

variable (W) [IsTopologicalAddGroup W]

/--
Definition of `decompLinearEquiv` / `decompLinearEquiv` 的定义

English:
definition decompLinearEquiv
  signature: : (V ->ᴬ[R] W) ≃ₗ[S] W × (V ->L[R] W) where
  body: decompEquiv R V W
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]

中文:
定义 decompLinearEquiv
  签名: : (V ->ᴬ[R] W) ≃ₗ[S] W × (V ->L[R] W) where
  定义体: decompEquiv R V W
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]

Depends on / 依赖: decompEquiv
-/
def decompLinearEquiv : (V ->ᴬ[R] W) ≃ₗ[S] W × (V ->L[R] W) where
  __ := decompEquiv R V W
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/--
theorem `fst_decompLinearEquiv` / 定理 `fst_decompLinearEquiv`

English:
theorem fst_decompLinearEquiv
  given: (f : V ->ᴬ[R] W)
  proof: rfl

@[simp]

中文:
定理 fst_decompLinearEquiv
  条件: (f : V ->ᴬ[R] W)
  证明: rfl

@[simp]
-/
theorem fst_decompLinearEquiv (f : V ->ᴬ[R] W) :
    (decompLinearEquiv R S V W f).1 = f 0 :=
  rfl

@[simp]
/--
theorem `snd_decompLinearEquiv` / 定理 `snd_decompLinearEquiv`

English:
theorem snd_decompLinearEquiv
  given: (f : V ->ᴬ[R] W)
  proof: rfl

@[simp]

中文:
定理 snd_decompLinearEquiv
  条件: (f : V ->ᴬ[R] W)
  证明: rfl

@[simp]
-/
theorem snd_decompLinearEquiv (f : V ->ᴬ[R] W) :
    (decompLinearEquiv R S V W f).2 = f.contLinear :=
  rfl

@[simp]
/--
theorem `decompLinearEquiv_symm_apply` / 定理 `decompLinearEquiv_symm_apply`

English:
theorem decompLinearEquiv_symm_apply
  given: (p : W × (V ->L[R] W)) (x : V)
  proof: rfl

中文:
定理 decompLinearEquiv_symm_apply
  条件: (p : W × (V ->L[R] W)) (x : V)
  证明: rfl
-/
theorem decompLinearEquiv_symm_apply (p : W × (V ->L[R] W)) (x : V) :
    (decompLinearEquiv R S V W).symm p x = p.2 x + p.1 :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `decompLinearEquiv_symm_contLinear` / 定理 `decompLinearEquiv_symm_contLinear`

English:
theorem decompLinearEquiv_symm_contLinear
  given: (p : W × (V ->L[R] W))
  proof: by
  ext; simp [decompLinearEquiv]

中文:
定理 decompLinearEquiv_symm_contLinear
  条件: (p : W × (V ->L[R] W))
  证明: by
  ext; simp [decompLinearEquiv]

Depends on / 依赖: decompLinearEquiv
-/
theorem decompLinearEquiv_symm_contLinear (p : W × (V ->L[R] W)) :
    ((decompLinearEquiv R S V W).symm p).contLinear = p.2 := by
  ext; simp [decompLinearEquiv]

end

section

variable [IsTopologicalAddGroup W] [IsTopologicalAddTorsor Q]

/-- The space of continuous affine maps from a topological vector space to a topological affine
space is affinely isomorphic to the product of the codomain with the space of linear maps, by taking
the value of the affine map at `(0 : V)` and the linear part. -/
@[simps linear]
/--
Definition of `decompAffineEquiv` / `decompAffineEquiv` 的定义

English:
definition decompAffineEquiv
  signature: : (V ->ᴬ[R] Q) ≃ᵃ[S] Q × (V ->L[R] W) where
  body: decompEquiv R V Q
  linear := decompLinearEquiv R S V W
  map_vadd' _ _ := rfl

@[simp]

中文:
定义 decompAffineEquiv
  签名: : (V ->ᴬ[R] Q) ≃ᵃ[S] Q × (V ->L[R] W) where
  定义体: decompEquiv R V Q
  linear := decompLinearEquiv R S V W
  map_vadd' _ _ := rfl

@[simp]

Depends on / 依赖: decompEquiv
-/
def decompAffineEquiv : (V ->ᴬ[R] Q) ≃ᵃ[S] Q × (V ->L[R] W) where
  __ := decompEquiv R V Q
  linear := decompLinearEquiv R S V W
  map_vadd' _ _ := rfl

@[simp]
/--
theorem `fst_decompAffineEquiv` / 定理 `fst_decompAffineEquiv`

English:
theorem fst_decompAffineEquiv
  given: (f : V ->ᴬ[R] Q)
  proof: rfl

@[simp]

中文:
定理 fst_decompAffineEquiv
  条件: (f : V ->ᴬ[R] Q)
  证明: rfl

@[simp]
-/
theorem fst_decompAffineEquiv (f : V ->ᴬ[R] Q) :
    (decompAffineEquiv R S V Q f).1 = f 0 :=
  rfl

@[simp]
/--
theorem `snd_decompAffineEquiv` / 定理 `snd_decompAffineEquiv`

English:
theorem snd_decompAffineEquiv
  given: (f : V ->ᴬ[R] Q)
  proof: rfl

@[simp]

中文:
定理 snd_decompAffineEquiv
  条件: (f : V ->ᴬ[R] Q)
  证明: rfl

@[simp]
-/
theorem snd_decompAffineEquiv (f : V ->ᴬ[R] Q) :
    (decompAffineEquiv R S V Q f).2 = f.contLinear :=
  rfl

@[simp]
/--
theorem `decompAffineEquiv_symm_apply` / 定理 `decompAffineEquiv_symm_apply`

English:
theorem decompAffineEquiv_symm_apply
  given: (p : Q × (V ->L[R] W)) (x : V)
  proof: rfl

@[simp]

中文:
定理 decompAffineEquiv_symm_apply
  条件: (p : Q × (V ->L[R] W)) (x : V)
  证明: rfl

@[simp]
-/
theorem decompAffineEquiv_symm_apply (p : Q × (V ->L[R] W)) (x : V) :
    (decompAffineEquiv R S V Q).symm p x = p.2 x +ᵥ p.1 :=
  rfl

@[simp]
/--
theorem `decompAffineEquiv_symm_contLinear` / 定理 `decompAffineEquiv_symm_contLinear`

English:
theorem decompAffineEquiv_symm_contLinear
  given: (p : Q × (V ->L[R] W))
  proof: by
  rw [decompAffineEquiv]; rw [← AffineEquiv.coe_symm_toEquiv]; rw [decompEquiv_symm_contLinear]

中文:
定理 decompAffineEquiv_symm_contLinear
  条件: (p : Q × (V ->L[R] W))
  证明: by
  rw [decompAffineEquiv]; rw [← AffineEquiv.coe_symm_toEquiv]; rw [decompEquiv_symm_contLinear]

Depends on / 依赖: AffineEquiv, AffineEquiv.coe_symm_toEquiv, coe_symm_toEquiv, decompAffineEquiv, decompEquiv_symm_contLinear
-/
theorem decompAffineEquiv_symm_contLinear (p : Q × (V ->L[R] W)) :
    ((decompAffineEquiv R S V Q).symm p).contLinear = p.2 := by
  rw [decompAffineEquiv]; rw [← AffineEquiv.coe_symm_toEquiv]; rw [decompEquiv_symm_contLinear]

end

end ContinuousAffineMap
