/-
Copyright (c) 2022 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Cone.Closure
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import Mathlib.Topology.Algebra.Order.Module
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Proper cones

We define a *proper cone* as a closed, pointed cone. Proper cones are used in defining conic
programs which generalize linear programs. A linear program is a conic program for the positive
cone. We then prove Farkas' lemma for conic programs following the proof in the reference below.
Farkas' lemma is equivalent to strong duality. So, once we have the definitions of conic and
linear programs, the results from this file can be used to prove duality theorems.

One can turn `C : PointedCone R E` + `hC : IsClosed C` into `C : ProperCone R E` in a tactic block
by doing `lift C to ProperCone R E using hC`.

One can also turn `C : ConvexCone 𝕜 E` + `hC : Set.Nonempty C ∧ IsClosed C` into
`C : ProperCone 𝕜 E` in a tactic block by doing `lift C to ProperCone 𝕜 E using hC`,
assuming `𝕜` is a dense topological field.

## TODO

The next steps are:
- Add `ConvexConeClass` that extends `SetLike` and replace the below instance
- Define primal and dual cone programs and prove weak duality.
- Prove regular and strong duality for cone programs using Farkas' lemma (see reference).
- Define linear programs and prove LP duality as a special case of cone duality.
- Find a better reference (textbook instead of lecture notes).

## References

- [B. Gartner and J. Matousek, Cone Programming][gartnerMatousek]

-/

@[expose] public section

open ContinuousLinearMap Filter Function Set

variable {𝕜 R E F G : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [TopologicalSpace E] [Module R E]
variable [AddCommMonoid F] [TopologicalSpace F] [Module R F]
variable [AddCommMonoid G] [TopologicalSpace G] [Module R G]

local notation "R≥0" => {r : R // 0 ≤ r}

variable (R E) in
/-- A proper cone is a pointed cone `C` that is closed. Proper cones have the nice property that
they are equal to their double dual, see `ProperCone.dual_dual`.
This makes them useful for defining cone programs and proving duality theorems. -/
/-
**ProperCone** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ProperCone
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
A proper cone is a pointed cone `C` that is closed. Proper cones have the nice p
roperty that
they are equal to their double dual, see `ProperCone.dual_dual`.
This makes them useful for defining cone programs and proving duality theorems.
-/
abbrev ProperCone := ClosedSubmodule R≥0 E

namespace ProperCone
section Module
variable {C C₁ C₂ : ProperCone R E} {r : R} {x : E}

/-- Any proper cone can be seen as a pointed cone.

This is an alias of `ClosedSubmodule.toSubmodule` for convenience and discoverability. -/
/-
**ProperCone.toPointedCone** 是 Mathlib 中的一个定义，位于命名空间 `ProperCone`。
形式化陈述：{R : Type u_2} →   {E : Type u_3} →     [inst : Semiring R] →       [inst_
1 : PartialOrder R] →         [inst_2 : IsOrderedRing R] →           [inst_3 : A
ddCommMonoid E] →             [inst_4 : TopologicalSpace E] → [inst_5 : _root_.M
odule R E] → ProperCone R E → PointedCone R E
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
Any proper cone can be seen as a pointed cone.

This is an alias of `ClosedSubmodule.toSubmodule` for convenience and discoverab
ility.
-/
@[coe] abbrev toPointedCone (C : ProperCone R E) : PointedCone R E := C.toSubmodule
/-
**ProperCone.** 是 Mathlib 中的一个实例，位于命名空间 `ProperCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any proper cone can be seen as a pointed cone.

This is an alias of `ClosedSubmodule.toSubmodule` for convenience and discoverab
ility.
-/
instance : Coe (ProperCone R E) (PointedCone R E) := ⟨toPointedCone⟩
/-
**ProperCone.toPointedCone_injective** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：toPointedCone_injective : Injective ((↑) : ProperCone R E -> PointedCone R
 E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ClosedSubmodule.toSubmodule_injective`：toSubmodule_injective : Injective
 (toSubmodule : ClosedSubmodule R M -> Submodule R M)
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma toPointedCone_injective : Injective ((↑) : ProperCone R E → PointedCone R E) :=
  ClosedSubmodule.toSubmodule_injective

-- TODO: add `ConvexConeClass` that extends `SetLike` and replace the below instance
/-
**ProperCone.** 是 Mathlib 中的一个实例，位于命名空间 `ProperCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (ProperCone R E) E where
  coe C := C.carrier
  coe_injective _ _ h := ProperCone.toPointedCone_injective <| SetLike.coe_injective h
/-
**ProperCone.** 是 Mathlib 中的一个实例，位于命名空间 `ProperCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (ProperCone R E) := .ofSetLike (ProperCone R E) E
/-
**ProperCone.ext** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [inst_4 : Topologica
lSpace E] [inst_5 : _root_.Module R E] {C₁ C₂ : ProperCone R E},   (∀ (x : E), x
 ∈ C₁ ↔ x ∈ C₂) → C₁ = C₂
参数：∀ (x : E), x ∈ C₁ ↔ x ∈ C₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
@[ext] lemma ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h
/-
**ProperCone.mem_toPointedCone** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：mem_toPointedCone : x in C.toPointedCone ↔ x in C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma mem_toPointedCone : x ∈ C.toPointedCone ↔ x ∈ C := .rfl
/-
**ProperCone.pointed_toConvexCone** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：pointed_toConvexCone (C : ProperCone R E) : (C : ConvexCone R E).Pointed
参数：C : ProperCone R E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PointedCone.pointed_toConvexCone`：pointed_toConvexCone (C : PointedCone 
R E) : (C : ConvexCone R E).Pointed
-/
lemma pointed_toConvexCone (C : ProperCone R E) : (C : ConvexCone R E).Pointed :=
  C.toPointedCone.pointed_toConvexCone
/-
**ProperCone.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [inst_4 : Topologica
lSpace E] [inst_5 : _root_.Module R E] (C : ProperCone R E),   (↑C).Nonempty
参数：C : ProperCone R E；↑C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.nonempty`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), (↑p
).Nonemp…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
protected lemma nonempty (C : ProperCone R E) : (C : Set E).Nonempty := C.toSubmodule.nonempty
/-
**ProperCone.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [inst_4 : Topologica
lSpace E] [inst_5 : _root_.Module R E] (C : ProperCone R E),   IsClosed ↑C
参数：C : ProperCone R E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.isClosed'`：∀ {R : Type u_2} {M : Type u_3} [inst : Semir
ing R] [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M]   [inst_3 : _roo
t_.Module R M] …
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
protected lemma isClosed (C : ProperCone R E) : IsClosed (C : Set E) := C.isClosed'
/-
**ProperCone.convex** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [inst_4 : Topologica
lSpace E] [inst_5 : _root_.Module R E] (C : ProperCone R E),   Convex R ↑C
参数：C : ProperCone R E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PointedCone.convex`：convex (C : PointedCone R E) : Convex R (C : Set E)
-/
protected lemma convex (C : ProperCone R E) : Convex R (C : Set E) := C.toPointedCone.convex

protected nonrec lemma smul_mem (C : ProperCone R E) (hx : x ∈ C) (hr : 0 ≤ r) : r • x ∈ C :=
  C.smul_mem ⟨r, hr⟩ hx

section T1Space
variable [T1Space E]

/-
**ProperCone.mem_bot** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：mem_bot : x in (⊥ : ProperCone R E) ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma mem_bot : x ∈ (⊥ : ProperCone R E) ↔ x = 0 := .rfl
/-
**ProperCone.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [inst_4 : Topologica
lSpace E] [inst_5 : _root_.Module R E] [inst_6 : T1Space E], ↑⊥ = {0}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
@[simp, norm_cast] lemma coe_bot : (⊥ : ProperCone R E) = ({0} : Set E) := rfl
/-
**ProperCone.toPointedCone_bot** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [inst_4 : Topologica
lSpace E] [inst_5 : _root_.Module R E] [inst_6 : T1Space E], ↑⊥ = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
@[simp, norm_cast] lemma toPointedCone_bot : (⊥ : ProperCone R E).toPointedCone = ⊥ := rfl

end T1Space

/-- The closure of image of a proper cone under an `R`-linear map is a proper cone. We
use continuous maps here so that the comap of f is also a map between proper cones. -/
/-
**ProperCone.comap** 是 Mathlib 中的一个缩写定义，位于命名空间 `ProperCone`。
形式化陈述：comap (f : E ->L[R] F) (C : ProperCone R F) : ProperCone R E
参数：f : E ->L[R] F；C : ProperCone R F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
The closure of image of a proper cone under an `R`-linear map is a proper cone. 
We
use continuous maps here so that the comap of f is also a map between proper con
es.
-/
abbrev comap (f : E →L[R] F) (C : ProperCone R F) : ProperCone R E :=
  ClosedSubmodule.comap (f.restrictScalars R≥0) C
/-
**ProperCone.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_2} {F : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid F] [inst_4 : Topologica
lSpace F] [inst_5 : _root_.Module R F] (C : ProperCone R F),   ProperCone.comap 
(ContinuousLinearMap.id R F) C = C
参数：C : ProperCone R F；ContinuousLinearMap.id R F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comap_id (C : ProperCone R F) : C.comap (.id _ _) = C := rfl
/-
**ProperCone.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Semiring R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [inst
_4 : TopologicalSpace E] [inst_5 : _root_.Module R E] [inst_6 : AddCommMonoid F]
   [inst_7 : TopologicalSpace F] [inst_8 : _root_.Module R F] (f : E →L[R] F) (C
 : ProperCone R F),   ↑(ProperCone.comap f C) = ⇑f ⁻¹' ↑C
参数：f : E →L[R] F；C : ProperCone R F；ProperCone.comap f C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_comap (f : E →L[R] F) (C : ProperCone R F) : (C.comap f : Set E) = f ⁻¹' C := rfl
/-
**ProperCone.comap_comap** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：comap_comap (g : F ->L[R] G) (f : E ->L[R] F) (C : ProperCone R G) : (C.co
map g).comap f = C.comap (g.comp f)
参数：g : F ->L[R] G；f : E ->L[R] F；C : ProperCone R G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_comap (g : F →L[R] G) (f : E →L[R] F) (C : ProperCone R G) :
    (C.comap g).comap f = C.comap (g.comp f) := rfl
/-
**ProperCone.mem_comap** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：mem_comap {C : ProperCone R F} {f : E ->L[R] F} : x in C.comap f ↔ f x in 
C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_comap {C : ProperCone R F} {f : E →L[R] F} : x ∈ C.comap f ↔ f x ∈ C := .rfl

variable [ContinuousAdd F] [ContinuousConstSMul R F]

/-- The closure of image of a proper cone under a linear map is a proper cone.

We use continuous maps here to match `ProperCone.comap`. -/
/-
**ProperCone.map** 是 Mathlib 中的一个缩写定义，位于命名空间 `ProperCone`。
形式化陈述：map (f : E ->L[R] F) (C : ProperCone R E) : ProperCone R F
参数：f : E ->L[R] F；C : ProperCone R E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
The closure of image of a proper cone under a linear map is a proper cone.

We use continuous maps here to match `ProperCone.comap`.
-/
abbrev map (f : E →L[R] F) (C : ProperCone R E) : ProperCone R F :=
  ClosedSubmodule.map (f.restrictScalars R≥0) C
/-
**ProperCone.map_id** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_2} {F : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid F] [inst_4 : Topologica
lSpace F] [inst_5 : _root_.Module R F] [inst_6 : ContinuousAdd F]   [inst_7 : Co
ntinuousConstSMul R F] (C : ProperCone R F), ProperCone.map (ContinuousLinearMap
.id R F) C = C
参数：C : ProperCone R F；ContinuousLinearMap.id R F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ClosedSubmodule.map_id`：map_id [ContinuousAdd M] [ContinuousConstSMul R 
M] (s : ClosedSubmodule R M) : s.map (.id _ _) = s
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
@[simp] lemma map_id (C : ProperCone R F) : C.map (.id _ _) = C := ClosedSubmodule.map_id _

@[simp, norm_cast]
/-
**ProperCone.coe_map** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：coe_map (f : E ->L[R] F) (C : ProperCone R E) : C.map f = (C.toPointedCone
.map (f : E ->ₗ[R] F)).closure
参数：f : E ->L[R] F；C : ProperCone R E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_map (f : E →L[R] F) (C : ProperCone R E) :
    C.map f = (C.toPointedCone.map (f : E →ₗ[R] F)).closure := rfl

@[simp]
/-
**ProperCone.mem_map** 是 Mathlib 中的一个引理，位于命名空间 `ProperCone`。
形式化陈述：mem_map {f : E ->L[R] F} {C : ProperCone R E} {y : F} : y in C.map f ↔ y i
n (C.toPointedCone.map (f : E ->ₗ[R] F)).closure
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_map {f : E →L[R] F} {C : ProperCone R E} {y : F} :
    y ∈ C.map f ↔ y ∈ (C.toPointedCone.map (f : E →ₗ[R] F)).closure := .rfl

end Module

section PositiveCone
variable [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono R E] [OrderClosedTopology E] {x : E}

variable (R E) in
/-- The positive cone is the proper cone formed by the set of nonnegative elements in an ordered
module. -/
@[simps!]
/-
**ProperCone.positive** 是 Mathlib 中的一个定义，位于命名空间 `ProperCone`。
形式化陈述：positive : ProperCone R E where toSubmodule
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
The positive cone is the proper cone formed by the set of nonnegative elements i
n an ordered
module.
-/
def positive : ProperCone R E where
  toSubmodule := PointedCone.positive R E
  isClosed' := isClosed_Ici
/-
**ProperCone.mem_positive** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [inst_4 : Topologica
lSpace E] [inst_5 : _root_.Module R E] [inst_6 : PartialOrder E]   [inst_7 : IsO
rderedAddMonoid E] [inst_8 : PosSMulMono R E] [inst_9 : OrderClosedTopology E] {
x : E},   x ∈ ProperCone.positive R E ↔ 0 ≤ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_positive : x ∈ positive R E ↔ 0 ≤ x := .rfl
/-
**ProperCone.toPointedCone_positive** 是 Mathlib 中的一个定理，位于命名空间 `ProperCone`。
形式化陈述：∀ {R : Type u_2} {E : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [inst_4 : Topologica
lSpace E] [inst_5 : _root_.Module R E] [inst_6 : PartialOrder E]   [inst_7 : IsO
rderedAddMonoid E] [inst_8 : PosSMulMono R E] [inst_9 : OrderClosedTopology E], 
  ↑(ProperCone.positive R E) = PointedCone.positive R E
参数：ProperCone.positive R E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toPointedCone_positive : (positive R E).toPointedCone = .positive R E := rfl

end PositiveCone
end ProperCone

/-!
### Topological properties of convex cones

This section proves topological results about convex cones.

#### TODO

This result generalises to G-submodules.
-/

namespace ConvexCone
variable [Semifield 𝕜] [LinearOrder 𝕜] [Module 𝕜 E] {s : Set E}

-- FIXME: This is necessary for the proof below but triggers the `unusedSectionVars` linter.
-- variable [IsStrictOrderedRing 𝕜] [IsTopologicalAddGroup M] in
/-- This is true essentially by `Submodule.span_eq_iUnion_nat`, except that `Submodule` currently
doesn't support that use case. See
https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/G-submodules/with/514426583 -/
proof_wanted isOpen_hull (hs : IsOpen s) : IsOpen (hull 𝕜 s : Set E)

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
  [ContinuousSMul 𝕜 E] {C : ConvexCone 𝕜 E}

/-
**ConvexCone.Pointed.of_nonempty_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCo
ne.Pointed`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : AddCommMonoid E] [inst_1 : Topolog
icalSpace E] [inst_2 : Semifield 𝕜]   [inst_3 : LinearOrder 𝕜] [inst_4 : _root_.
Module 𝕜 E] [inst_5 : TopologicalSpace 𝕜] [OrderTopology 𝕜]   [DenselyOrdered 𝕜]
 [NoMaxOrder 𝕜] [ContinuousSMul 𝕜 E] {C : ConvexCone 𝕜 E}, (↑C).Nonempty → IsClo
sed ↑C → C.Pointed
参数：↑C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `ConvexCone.smul_mem`：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] (C :
 ConvexCo…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `ContinuousAt.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalS
pace Y] [in…
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `ContinuousWithinAt.mem_closure_image`：ContinuousWithinAt.mem_closure_ima
ge (h : ContinuousWithinAt f s x) (hx : x in closure s) : f x in closure (f '' s
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `closure_Ioi`：closure_Ioi (a : α) [NoMaxOrder α] : closure (Ioi a) = Ici 
a
-/
lemma Pointed.of_nonempty_of_isClosed (hC : (C : Set E).Nonempty) (hSclos : IsClosed (C : Set E)) :
    C.Pointed := by
  obtain ⟨x, hx⟩ := hC
  let f : 𝕜 → E := (· • x)
  -- The closure of `f (0, ∞)` is a subset of `C`
  have hfS : closure (f '' Set.Ioi 0) ⊆ C :=
    hSclos.closure_subset_iff.2 <| by rintro _ ⟨_, h, rfl⟩; exact C.smul_mem h hx
  -- `f` is continuous at `0` from the right
  have fc : ContinuousWithinAt f (Set.Ioi (0 : 𝕜)) 0 := by fun_prop
  -- `0 ∈ closure f (0, ∞) ⊆ C, 0 ∈ C`
  simpa [f, Pointed, ← SetLike.mem_coe] using hfS <| fc.mem_closure_image <| by simp

variable [IsOrderedRing 𝕜]
/-
**ConvexCone.canLift** 是 Mathlib 中的一个实例，位于命名空间 `ConvexCone`。
形式化陈述：canLift : CanLift (ConvexCone 𝕜 E) (ProperCone 𝕜 E) (↑) fun C => (C : Set 
E).Nonempty ∧ IsClosed (C : Set E) where prf C hC
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ConvexCone.Pointed.of_nonempty_of_isClosed`：∀ {𝕜 : Type u_1} {E : Type u
_3} [inst : AddCommMonoid E] [inst_1 : TopologicalSpace E] [inst_2 : Semifield 𝕜
]   [inst_3 : LinearOrder 𝕜] [in…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance canLift : CanLift (ConvexCone 𝕜 E) (ProperCone 𝕜 E) (↑)
    fun C ↦ (C : Set E).Nonempty ∧ IsClosed (C : Set E) where
  prf C hC := ⟨⟨C.toPointedCone <| .of_nonempty_of_isClosed hC.1 hC.2, hC.2⟩, rfl⟩

end ConvexCone

