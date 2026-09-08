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


/-- A continuous map of affine spaces -/
/-
**ContinuousAffineMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   {V : Type u_2} →     {W : Type u_3} →       (P : Type u
_4) →         (Q : Type u_5) →           [inst : Ring R] →             [inst_1 :
 AddCommGroup V] →               [_root_.Module R V] →                 [Topologi
calSpace P] →                   [AddTorsor V P] →                     [inst_5 : 
AddCommGroup W] →                       [_root_.Module R W] →                   
      [TopologicalSpace Q] → [AddTorsor W Q] → Type (max (max (max u_2 u_3) u_4)
 u_5)
参数：max (max u_2 u_3) u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous map of affine spaces
-/
structure ContinuousAffineMap (R : Type*) {V W : Type*} (P Q : Type*) [Ring R] [AddCommGroup V]
  [Module R V] [TopologicalSpace P] [AddTorsor V P] [AddCommGroup W] [Module R W]
  [TopologicalSpace Q] [AddTorsor W Q] extends P →ᵃ[R] Q where
  cont : Continuous toFun

/-- A continuous map of affine spaces -/
notation:25 P " →ᴬ[" R "] " Q => ContinuousAffineMap R P Q

namespace ContinuousAffineMap

variable {R V W P Q : Type*} [Ring R]
variable [AddCommGroup V] [Module R V] [TopologicalSpace P] [AddTorsor V P]
variable [AddCommGroup W] [Module R W] [TopologicalSpace Q] [AddTorsor W Q]

/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (P →ᴬ[R] Q) (P →ᵃ[R] Q) :=
  ⟨toAffineMap⟩

attribute [coe] ContinuousAffineMap.toAffineMap
/-
**ContinuousAffineMap.toAffineMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sAffineMap`。
形式化陈述：toAffineMap_injective {f g : P ->ᴬ[R] Q} (h : (f : P ->ᵃ[R] Q) = (g : P ->
ᵃ[R] Q)) : f = g
参数：h : (f : P ->ᵃ[R] Q) = (g : P ->ᵃ[R] Q)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toAffineMap_injective {f g : P →ᴬ[R] Q} (h : (f : P →ᵃ[R] Q) = (g : P →ᵃ[R] Q)) :
    f = g := by
  cases f
  cases g
  congr
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (P →ᴬ[R] Q) P Q where
  coe f := f.toAffineMap
  coe_injective _ _ h := toAffineMap_injective <| DFunLike.coe_injective h
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousMapClass (P →ᴬ[R] Q) P Q where
  map_continuous := cont
/-
**ContinuousAffineMap.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMa
p`。
形式化陈述：toFun_eq_coe (f : P ->ᴬ[R] Q) : f.toFun = ⇑f
参数：f : P ->ᴬ[R] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : P →ᴬ[R] Q) : f.toFun = ⇑f := rfl
/-
**ContinuousAffineMap.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineM
ap`。
形式化陈述：coe_injective : @Function.Injective (P ->ᴬ[R] Q) (P -> Q) (⇑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective : @Function.Injective (P →ᴬ[R] Q) (P → Q) (⇑) :=
  DFunLike.coe_injective

@[ext]
/-
**ContinuousAffineMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：ext {f g : P ->ᴬ[R] Q} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : P →ᴬ[R] Q} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h
/-
**ContinuousAffineMap.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：congr_fun {f g : P ->ᴬ[R] Q} (h : f = g) (x : P) : f x = g x
参数：h : f = g；x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem congr_fun {f g : P →ᴬ[R] Q} (h : f = g) (x : P) : f x = g x :=
  DFunLike.congr_fun h _

/-- Forgetting its algebraic properties, a continuous affine map is a continuous map. -/
/-
**ContinuousAffineMap.toContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffin
eMap`。
形式化陈述：toContinuousMap (f : P ->ᴬ[R] Q) : C(P, Q)
参数：f : P ->ᴬ[R] Q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineMap.cont`：∀ {R : Type u_1} {V : Type u_2} {W : Type u_3}
 {P : Type u_4} {Q : Type u_5} [inst : Ring R] [inst_1 : AddCommGroup V]   [inst
_2 : _root_.Mo…

--- 原说明 ---
Forgetting its algebraic properties, a continuous affine map is a continuous map
.
-/
def toContinuousMap (f : P →ᴬ[R] Q) : C(P, Q) :=
  ⟨f, f.cont⟩
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeHead (P →ᴬ[R] Q) C(P, Q) :=
  ⟨toContinuousMap⟩

@[simp]
/-
**ContinuousAffineMap.toContinuousMap_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
ffineMap`。
形式化陈述：toContinuousMap_coe (f : P ->ᴬ[R] Q) : f.toContinuousMap = ↑f
参数：f : P ->ᴬ[R] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousMap_coe (f : P →ᴬ[R] Q) : f.toContinuousMap = ↑f := rfl

@[simp, norm_cast]
/-
**ContinuousAffineMap.coe_toAffineMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffin
eMap`。
形式化陈述：coe_toAffineMap (f : P ->ᴬ[R] Q) : ((f : P ->ᵃ[R] Q) : P -> Q) = f
参数：f : P ->ᴬ[R] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAffineMap (f : P →ᴬ[R] Q) : ((f : P →ᵃ[R] Q) : P → Q) = f := rfl

@[simp, norm_cast]
/-
**ContinuousAffineMap.coe_to_continuousMap** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
AffineMap`。
形式化陈述：coe_to_continuousMap (f : P ->ᴬ[R] Q) : ((f : C(P, Q)) : P -> Q) = f
参数：f : P ->ᴬ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineMap.instContinuousMapClass`：∀ {R : Type u_1} {V : Type u
_2} {W : Type u_3} {P : Type u_4} {Q : Type u_5} [inst : Ring R] [inst_1 : AddCo
mmGroup V]   [inst_2 : _root_.Mo…
-/
theorem coe_to_continuousMap (f : P →ᴬ[R] Q) : ((f : C(P, Q)) : P → Q) = f := rfl
/-
**ContinuousAffineMap.to_continuousMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousAffineMap`。
形式化陈述：to_continuousMap_injective {f g : P ->ᴬ[R] Q} (h : (f : C(P, Q)) = (g : C(
P, Q))) : f = g
参数：h : (f : C(P, Q)) = (g : C(P, Q))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineMap.instContinuousMapClass`：∀ {R : Type u_1} {V : Type u
_2} {W : Type u_3} {P : Type u_4} {Q : Type u_5} [inst : Ring R] [inst_1 : AddCo
mmGroup V]   [inst_2 : _root_.Mo…
· 使用定理 `ContinuousAffineMap.ext`：ext {f g : P ->ᴬ[R] Q} (h : forall x, f x = g x
) : f = g
· 使用定理 `ContinuousMap.congr_fun`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f g : C(X, Y)},   f = g → ∀ (x : X),
 f x = g x
-/
theorem to_continuousMap_injective {f g : P →ᴬ[R] Q} (h : (f : C(P, Q)) = (g : C(P, Q))) :
    f = g := by
  ext a
  exact ContinuousMap.congr_fun h a

@[norm_cast]
/-
**ContinuousAffineMap.coe_toAffineMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAf
fineMap`。
形式化陈述：coe_toAffineMap_mk (f : P ->ᵃ[R] Q) (h) : ((⟨f, h⟩ : P ->ᴬ[R] Q) : P ->ᵃ[R
] Q) = f
参数：f : P ->ᵃ[R] Q；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAffineMap_mk (f : P →ᵃ[R] Q) (h) : ((⟨f, h⟩ : P →ᴬ[R] Q) : P →ᵃ[R] Q) = f := rfl

@[norm_cast]
/-
**ContinuousAffineMap.coe_continuousMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
AffineMap`。
形式化陈述：coe_continuousMap_mk (f : P ->ᵃ[R] Q) (h) : ((⟨f, h⟩ : P ->ᴬ[R] Q) : C(P, 
Q)) = ⟨f, h⟩
参数：f : P ->ᵃ[R] Q；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineMap.instContinuousMapClass`：∀ {R : Type u_1} {V : Type u
_2} {W : Type u_3} {P : Type u_4} {Q : Type u_5} [inst : Ring R] [inst_1 : AddCo
mmGroup V]   [inst_2 : _root_.Mo…
-/
theorem coe_continuousMap_mk (f : P →ᵃ[R] Q) (h) : ((⟨f, h⟩ : P →ᴬ[R] Q) : C(P, Q)) = ⟨f, h⟩ := rfl

@[simp]
/-
**ContinuousAffineMap.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：coe_mk (f : P ->ᵃ[R] Q) (h) : ((⟨f, h⟩ : P ->ᴬ[R] Q) : P -> Q) = f
参数：f : P ->ᵃ[R] Q；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : P →ᵃ[R] Q) (h) : ((⟨f, h⟩ : P →ᴬ[R] Q) : P → Q) = f := rfl

@[simp]
/-
**ContinuousAffineMap.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：mk_coe (f : P ->ᴬ[R] Q) (h) : (⟨(f : P ->ᵃ[R] Q), h⟩ : P ->ᴬ[R] Q) = f
参数：f : P ->ᴬ[R] Q；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineMap.ext`：ext {f g : P ->ᴬ[R] Q} (h : forall x, f x = g x
) : f = g
-/
theorem mk_coe (f : P →ᴬ[R] Q) (h) : (⟨(f : P →ᵃ[R] Q), h⟩ : P →ᴬ[R] Q) = f := by
  ext
  rfl

@[continuity]
/-
**ContinuousAffineMap.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`
。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {W : Type u_3} {P : Type u_4} {Q : Type u_
5} [inst : Ring R] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module R V] [ins
t_3 : TopologicalSpace P] [inst_4 : AddTorsor V P] [inst_5 : AddCommGroup W]   [
inst_6 : _root_.Module R W] [inst_7 : TopologicalSpace Q] [inst_8 : AddTorsor W 
Q] (f : P →ᴬ[R] Q), Continuous ⇑f
参数：f : P →ᴬ[R] Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineMap.cont`：∀ {R : Type u_1} {V : Type u_2} {W : Type u_3}
 {P : Type u_4} {Q : Type u_5} [inst : Ring R] [inst_1 : AddCommGroup V]   [inst
_2 : _root_.Mo…
-/
protected theorem continuous (f : P →ᴬ[R] Q) : Continuous f := f.2

variable (R P)

/-- The constant map as a continuous affine map -/
/-
**ContinuousAffineMap.const** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineMap`。
形式化陈述：const (q : Q) : P ->ᴬ[R] Q
参数：q : Q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)

--- 原说明 ---
The constant map as a continuous affine map
-/
def const (q : Q) : P →ᴬ[R] Q :=
  { AffineMap.const R P q with cont := continuous_const }

@[simp]
/-
**ContinuousAffineMap.coe_const** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：coe_const (q : Q) : ⇑(const R P q) = Function.const P q
参数：q : Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_const (q : Q) : ⇑(const R P q) = Function.const P q := rfl
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Inhabited (P →ᴬ[R] Q) :=
  ⟨const R P <| Nonempty.some (by infer_instance : Nonempty Q)⟩

/-- The identity map as a continuous affine map -/
/-
**ContinuousAffineMap.id** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineMap`。
形式化陈述：id : P ->ᴬ[R] P
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
The identity map as a continuous affine map
-/
def id : P →ᴬ[R] P := { AffineMap.id R P with cont := continuous_id }

@[simp, norm_cast]
/-
**ContinuousAffineMap.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：coe_id : ⇑(id R P) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(id R P) = _root_.id := rfl

variable {R P} {W₂ Q₂ W₃ Q₃ : Type*}
variable [AddCommGroup W₂] [Module R W₂] [TopologicalSpace Q₂] [AddTorsor W₂ Q₂]

/-- The composition of continuous affine maps as a continuous affine map -/
/-
**ContinuousAffineMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineMap`。
形式化陈述：comp (f : Q ->ᴬ[R] Q₂) (g : P ->ᴬ[R] Q) : P ->ᴬ[R] Q₂
参数：f : Q ->ᴬ[R] Q₂；g : P ->ᴬ[R] Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of continuous affine maps as a continuous affine map
-/
def comp (f : Q →ᴬ[R] Q₂) (g : P →ᴬ[R] Q) : P →ᴬ[R] Q₂ :=
  { (f : Q →ᵃ[R] Q₂).comp (g : P →ᵃ[R] Q) with cont := f.cont.comp g.cont }

@[simp, norm_cast]
/-
**ContinuousAffineMap.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：coe_comp (f : Q ->ᴬ[R] Q₂) (g : P ->ᴬ[R] Q) : ⇑(f.comp g) = f ∘ g
参数：f : Q ->ᴬ[R] Q₂；g : P ->ᴬ[R] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : Q →ᴬ[R] Q₂) (g : P →ᴬ[R] Q) : ⇑(f.comp g) = f ∘ g := rfl
/-
**ContinuousAffineMap.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`
。
形式化陈述：comp_apply (f : Q ->ᴬ[R] Q₂) (g : P ->ᴬ[R] Q) (p : P) : f.comp g p = f (g 
p)
参数：f : Q ->ᴬ[R] Q₂；g : P ->ᴬ[R] Q；p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : Q →ᴬ[R] Q₂) (g : P →ᴬ[R] Q) (p : P) : f.comp g p = f (g p) := rfl

@[simp]
/-
**ContinuousAffineMap.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：comp_id (f : P ->ᴬ[R] Q) : f.comp (id R P) = f
参数：f : P ->ᴬ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineMap.ext`：ext {f g : P ->ᴬ[R] Q} (h : forall x, f x = g x
) : f = g
-/
theorem comp_id (f : P →ᴬ[R] Q) : f.comp (id R P) = f :=
  ext fun _ => rfl

@[simp]
/-
**ContinuousAffineMap.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：id_comp (f : P ->ᴬ[R] Q) : (id R Q).comp f = f
参数：f : P ->ᴬ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineMap.ext`：ext {f g : P ->ᴬ[R] Q} (h : forall x, f x = g x
) : f = g
-/
theorem id_comp (f : P →ᴬ[R] Q) : (id R Q).comp f = f :=
  ext fun _ => rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying a `ContinuousAffineMap` commutes with `AffineMap.lineMap`. -/
@[simp]
/-
**ContinuousAffineMap.apply_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineM
ap`。
形式化陈述：apply_lineMap (f : P ->ᴬ[R] Q) (p₀ p₁ : P) (c : R) : f (AffineMap.lineMap 
p₀ p₁ c) = AffineMap.lineMap (f p₀) (f p₁) c
参数：f : P ->ᴬ[R] Q；p₀ p₁ : P；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousAffineMap.coe_toAffineMap`：coe_toAffineMap (f : P ->ᴬ[R] Q) : 
((f : P ->ᵃ[R] Q) : P -> Q) = f
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c

--- 原说明 ---
Applying a `ContinuousAffineMap` commutes with `AffineMap.lineMap`.
-/
theorem apply_lineMap (f : P →ᴬ[R] Q) (p₀ p₁ : P) (c : R) :
    f (AffineMap.lineMap p₀ p₁ c) = AffineMap.lineMap (f p₀) (f p₁) c := by
  rw [← ContinuousAffineMap.coe_toAffineMap, AffineMap.apply_lineMap]

/-- The continuous affine map sending `0` to `p₀` and `1` to `p₁` -/
/-
**ContinuousAffineMap.lineMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineMap`。
形式化陈述：lineMap (p₀ p₁ : P) [TopologicalSpace R] [TopologicalSpace V] [ContinuousS
Mul R V] [ContinuousVAdd V P] : R ->ᴬ[R] P where toAffineMap
参数：p₀ p₁ : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous affine map sending `0` to `p₀` and `1` to `p₁`
-/
def lineMap (p₀ p₁ : P) [TopologicalSpace R] [TopologicalSpace V]
    [ContinuousSMul R V] [ContinuousVAdd V P] : R →ᴬ[R] P where
  toAffineMap := AffineMap.lineMap p₀ p₁
  cont := (continuous_id.smul continuous_const).vadd continuous_const
/-
**ContinuousAffineMap.lineMap_toAffineMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
ffineMap`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module R V]   [inst_3 : TopologicalSpace P] [ins
t_4 : AddTorsor V P] (p₀ p₁ : P) [inst_5 : TopologicalSpace R]   [inst_6 : Topol
ogicalSpace V] [inst_7 : ContinuousSMul R V] [inst_8 : ContinuousVAdd V P],   ↑(
ContinuousAffineMap.lineMap p₀ p₁) = AffineMap.lineMap p₀ p₁
参数：p₀ p₁ : P；ContinuousAffineMap.lineMap p₀ p₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lineMap_toAffineMap (p₀ p₁ : P) [TopologicalSpace R] [TopologicalSpace V]
    [ContinuousSMul R V] [ContinuousVAdd V P] :
    (lineMap p₀ p₁).toAffineMap = AffineMap.lineMap (k := R) p₀ p₁ := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**ContinuousAffineMap.coe_lineMap_eq** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousAffine
Map`。
形式化陈述：coe_lineMap_eq (p₀ p₁ : P) [TopologicalSpace R] [TopologicalSpace V] [Cont
inuousSMul R V] [ContinuousVAdd V P] : ⇑(ContinuousAffineMap.lineMap p₀ p₁) = ⇑(
AffineMap.lineMap (k
参数：p₀ p₁ : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_lineMap_eq (p₀ p₁ : P) [TopologicalSpace R] [TopologicalSpace V]
    [ContinuousSMul R V] [ContinuousVAdd V P] :
    ⇑(ContinuousAffineMap.lineMap p₀ p₁) = ⇑(AffineMap.lineMap (k := R) p₀ p₁) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying a `ContinuousAffineMap` commutes with `ContinuousAffineMap.lineMap`. -/
@[simp]
/-
**ContinuousAffineMap.apply_lineMap'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffine
Map`。
形式化陈述：apply_lineMap' [TopologicalSpace R] [TopologicalSpace V] [TopologicalSpace
 W] [ContinuousSMul R V] [ContinuousSMul R W] [ContinuousVAdd V P] [ContinuousVA
dd W Q] (f : P ->ᴬ[R] Q) (p₀ p₁ : P) (c : R) : f (lineMap p₀ p₁ c) = lineMap (f 
p₀) (f p₁) c
参数：f : P ->ᴬ[R] Q；p₀ p₁ : P；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAffineMap.apply_lineMap`：apply_lineMap (f : P ->ᴬ[R] Q) (p₀ p₁
 : P) (c : R) : f (AffineMap.lineMap p₀ p₁ c) = AffineMap.lineMap (f p₀) (f p₁) 
c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Applying a `ContinuousAffineMap` commutes with `ContinuousAffineMap.lineMap`.
-/
theorem apply_lineMap' [TopologicalSpace R] [TopologicalSpace V] [TopologicalSpace W]
    [ContinuousSMul R V] [ContinuousSMul R W] [ContinuousVAdd V P] [ContinuousVAdd W Q]
    (f : P →ᴬ[R] Q) (p₀ p₁ : P) (c : R) :
    f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c := by
  simp_rw [coe_lineMap_eq, apply_lineMap]

section IsTopologicalAddTorsor

variable [TopologicalSpace V] [IsTopologicalAddTorsor P]
variable [TopologicalSpace W] [IsTopologicalAddTorsor Q]
variable [TopologicalSpace W₂] [IsTopologicalAddTorsor Q₂]

/-- The linear map underlying a continuous affine map is continuous. -/
/-
**ContinuousAffineMap.contLinear** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineMap`
。
形式化陈述：contLinear (f : P ->ᴬ[R] Q) : V ->L[R] W
参数：f : P ->ᴬ[R] Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map underlying a continuous affine map is continuous.
-/
def contLinear (f : P →ᴬ[R] Q) : V →L[R] W :=
  { f.linear with
    toFun := f.linear
    cont := by rw [AffineMap.continuous_linear_iff]; exact f.cont }

@[simp]
/-
**ContinuousAffineMap.coe_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffine
Map`。
形式化陈述：coe_contLinear (f : P ->ᴬ[R] Q) : (f.contLinear : V -> W) = f.linear
参数：f : P ->ᴬ[R] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_contLinear (f : P →ᴬ[R] Q) : (f.contLinear : V → W) = f.linear :=
  rfl

@[simp]
/-
**ContinuousAffineMap.coe_contLinear_eq_linear** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousAffineMap`。
形式化陈述：coe_contLinear_eq_linear (f : P ->ᴬ[R] Q) : (f.contLinear : V ->ₗ[R] W) = 
(f : P ->ᵃ[R] Q).linear
参数：f : P ->ᴬ[R] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_contLinear_eq_linear (f : P →ᴬ[R] Q) :
    (f.contLinear : V →ₗ[R] W) = (f : P →ᵃ[R] Q).linear :=
  rfl

@[simp]
/-
**ContinuousAffineMap.coe_mk_contLinear_eq_linear** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousAffineMap`。
形式化陈述：coe_mk_contLinear_eq_linear (f : P ->ᵃ[R] Q) (h) : ((⟨f, h⟩ : P ->ᴬ[R] Q).
contLinear : V -> W) = f.linear
参数：f : P ->ᵃ[R] Q；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk_contLinear_eq_linear (f : P →ᵃ[R] Q) (h) :
    ((⟨f, h⟩ : P →ᴬ[R] Q).contLinear : V → W) = f.linear :=
  rfl
/-
**ContinuousAffineMap.coe_linear_eq_coe_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousAffineMap`。
形式化陈述：coe_linear_eq_coe_contLinear (f : P ->ᴬ[R] Q) : ((f : P ->ᵃ[R] Q).linear :
 V -> W) = (⇑f.contLinear : V -> W)
参数：f : P ->ᴬ[R] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_linear_eq_coe_contLinear (f : P →ᴬ[R] Q) :
    ((f : P →ᵃ[R] Q).linear : V → W) = (⇑f.contLinear : V → W) :=
  rfl

@[simp]
/-
**ContinuousAffineMap.comp_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffin
eMap`。
形式化陈述：comp_contLinear (f : P ->ᴬ[R] Q) (g : Q ->ᴬ[R] Q₂) : (g.comp f).contLinear
 = g.contLinear.comp f.contLinear
参数：f : P ->ᴬ[R] Q；g : Q ->ᴬ[R] Q₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_contLinear (f : P →ᴬ[R] Q) (g : Q →ᴬ[R] Q₂) :
    (g.comp f).contLinear = g.contLinear.comp f.contLinear :=
  rfl

@[simp]
/-
**ContinuousAffineMap.map_vadd** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：map_vadd (f : P ->ᴬ[R] Q) (p : P) (v : V) : f (v +ᵥ p) = f.contLinear v +ᵥ
 f p
参数：f : P ->ᴬ[R] Q；p : P；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.map_vadd'`：∀ {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V
2 : Type u_4} {P2 : Type u_5} [inst : Ring k]   [inst_1 : AddCommGroup V1] [inst
_2 : _roo…
-/
theorem map_vadd (f : P →ᴬ[R] Q) (p : P) (v : V) : f (v +ᵥ p) = f.contLinear v +ᵥ f p :=
  f.map_vadd' p v

@[simp]
/-
**ContinuousAffineMap.contLinear_map_vsub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
ffineMap`。
形式化陈述：contLinear_map_vsub (f : P ->ᴬ[R] Q) (p₁ p₂ : P) : f.contLinear (p₁ -ᵥ p₂)
 = f p₁ -ᵥ f p₂
参数：f : P ->ᴬ[R] Q；p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
-/
theorem contLinear_map_vsub (f : P →ᴬ[R] Q) (p₁ p₂ : P) : f.contLinear (p₁ -ᵥ p₂) = f p₁ -ᵥ f p₂ :=
  f.toAffineMap.linearMap_vsub p₁ p₂

@[simp]
/-
**ContinuousAffineMap.const_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffi
neMap`。
形式化陈述：const_contLinear (q : Q) : (const R P q).contLinear = 0
参数：q : Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_contLinear (q : Q) : (const R P q).contLinear = 0 :=
  rfl
/-
**ContinuousAffineMap.contLinear_eq_zero_iff_exists_const** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousAffineMap`。
形式化陈述：contLinear_eq_zero_iff_exists_const (f : P ->ᴬ[R] Q) : f.contLinear = 0 ↔ 
exists q, f = const R P q
参数：f : P ->ᴬ[R] Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousAffineMap.coe_contLinear_eq_linear`：coe_contLinear_eq_linear (
f : P ->ᴬ[R] Q) : (f.contLinear : V ->ₗ[R] W) = (f : P ->ᵃ[R] Q).linear
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousAffineMap.coe_linear_eq_coe_contLinear`：coe_linear_eq_coe_cont
Linear (f : P ->ᴬ[R] Q) : ((f : P ->ᵃ[R] Q).linear : V -> W) = (⇑f.contLinear : 
V -> W)
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `ContinuousAffineMap.ext`：ext {f g : P ->ᴬ[R] Q} (h : forall x, f x = g x
) : f = g
· 使用定理 `ContinuousAffineMap.coe_toAffineMap`：coe_toAffineMap (f : P ->ᴬ[R] Q) : 
((f : P ->ᵃ[R] Q) : P -> Q) = f
· 使用定理 `AffineMap.const_apply`：const_apply (p : P2) (q : P1) : (const k P1 p) q 
= p
· 使用定理 `ContinuousAffineMap.coe_const`：coe_const (q : Q) : ⇑(const R P q) = Func
tion.const P q
· 使用定理 `Function.const_apply`：∀ {β : Sort u_1} {α : Sort u_2} {y : β} {x : α}, F
unction.const α y x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineMap.linear_eq_zero_iff_exists_const`：linear_eq_zero_iff_exists_con
st (f : P1 ->ᵃ[k] P2) : f.linear = 0 ↔ exists q, f = const k P1 q
-/
theorem contLinear_eq_zero_iff_exists_const (f : P →ᴬ[R] Q) :
    f.contLinear = 0 ↔ ∃ q, f = const R P q := by
  have h₁ : f.contLinear = 0 ↔ (f : P →ᵃ[R] Q).linear = 0 := by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> ext
    · rw [← coe_contLinear_eq_linear, h]; rfl
    · rw [← coe_linear_eq_coe_contLinear, h]; rfl
  have h₂ : ∀ q : Q, f = const R P q ↔ (f : P →ᵃ[R] Q) = AffineMap.const R P q := by
    intro q
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> ext
    · rw [h]; rfl
    · rw [← coe_toAffineMap, h, AffineMap.const_apply, coe_const, Function.const_apply]
  simp_rw [h₁, h₂]
  exact (f : P →ᵃ[R] Q).linear_eq_zero_iff_exists_const

end IsTopologicalAddTorsor

section ModuleValuedMaps

variable {S : Type*}
variable [TopologicalSpace W]

/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (P →ᴬ[R] W) :=
  ⟨ContinuousAffineMap.const R P 0⟩

@[norm_cast, simp]
/-
**ContinuousAffineMap.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：coe_zero : ((0 : P ->ᴬ[R] W) : P -> W) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : P →ᴬ[R] W) : P → W) = 0 := rfl
/-
**ContinuousAffineMap.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`
。
形式化陈述：zero_apply (x : P) : (0 : P ->ᴬ[R] W) x = 0
参数：x : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (x : P) : (0 : P →ᴬ[R] W) x = 0 := rfl

section MulAction

variable [Monoid S] [DistribMulAction S W] [SMulCommClass R S W]
variable [ContinuousConstSMul S W]

/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul S (P →ᴬ[R] W) where
  smul t f := { t • (f : P →ᵃ[R] W) with cont := f.continuous.const_smul t }

@[norm_cast, simp]
/-
**ContinuousAffineMap.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：coe_smul (t : S) (f : P ->ᴬ[R] W) : ⇑(t • f) = t • ⇑f
参数：t : S；f : P ->ᴬ[R] W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (t : S) (f : P →ᴬ[R] W) : ⇑(t • f) = t • ⇑f := rfl
/-
**ContinuousAffineMap.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`
。
形式化陈述：smul_apply (t : S) (f : P ->ᴬ[R] W) (x : P) : (t • f) x = t • f x
参数：t : S；f : P ->ᴬ[R] W；x : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (t : S) (f : P →ᴬ[R] W) (x : P) : (t • f) x = t • f x := rfl
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribMulAction Sᵐᵒᵖ W] [IsCentralScalar S W] : IsCentralScalar S (P →ᴬ[R] W) where
  op_smul_eq_smul _ _ := ext fun _ ↦ op_smul_eq_smul _ _
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction S (P →ᴬ[R] W) :=
  Function.Injective.mulAction _ coe_injective coe_smul

variable [TopologicalSpace V] [IsTopologicalAddTorsor P] [IsTopologicalAddGroup W]

@[simp]
/-
**ContinuousAffineMap.smul_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffin
eMap`。
形式化陈述：smul_contLinear (t : S) (f : P ->ᴬ[R] W) : (t • f).contLinear = t • f.cont
Linear
参数：t : S；f : P ->ᴬ[R] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
-/
theorem smul_contLinear (t : S) (f : P →ᴬ[R] W) : (t • f).contLinear = t • f.contLinear :=
  rfl

end MulAction

variable [IsTopologicalAddGroup W]

/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (P →ᴬ[R] W) where
  add f g := { (f : P →ᵃ[R] W) + (g : P →ᵃ[R] W) with cont := f.continuous.add g.continuous }

@[norm_cast, simp]
/-
**ContinuousAffineMap.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：coe_add (f g : P ->ᴬ[R] W) : ⇑(f + g) = f + g
参数：f g : P ->ᴬ[R] W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (f g : P →ᴬ[R] W) : ⇑(f + g) = f + g := rfl
/-
**ContinuousAffineMap.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：add_apply (f g : P ->ᴬ[R] W) (x : P) : (f + g) x = f x + g x
参数：f g : P ->ᴬ[R] W；x : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply (f g : P →ᴬ[R] W) (x : P) : (f + g) x = f x + g x := rfl
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (P →ᴬ[R] W) where
  sub f g := { (f : P →ᵃ[R] W) - (g : P →ᵃ[R] W) with cont := f.continuous.sub g.continuous }

@[norm_cast, simp]
/-
**ContinuousAffineMap.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：coe_sub (f g : P ->ᴬ[R] W) : ⇑(f - g) = f - g
参数：f g : P ->ᴬ[R] W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (f g : P →ᴬ[R] W) : ⇑(f - g) = f - g := rfl
/-
**ContinuousAffineMap.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：sub_apply (f g : P ->ᴬ[R] W) (x : P) : (f - g) x = f x - g x
参数：f g : P ->ᴬ[R] W；x : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply (f g : P →ᴬ[R] W) (x : P) : (f - g) x = f x - g x := rfl
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (P →ᴬ[R] W) :=
  { neg := fun f => { -(f : P →ᵃ[R] W) with cont := f.continuous.neg } }

@[norm_cast, simp]
/-
**ContinuousAffineMap.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：coe_neg (f : P ->ᴬ[R] W) : ⇑(-f) = -f
参数：f : P ->ᴬ[R] W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (f : P →ᴬ[R] W) : ⇑(-f) = -f := rfl
/-
**ContinuousAffineMap.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：neg_apply (f : P ->ᴬ[R] W) (x : P) : (-f) x = -f x
参数：f : P ->ᴬ[R] W；x : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply (f : P →ᴬ[R] W) (x : P) : (-f) x = -f x := rfl
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (P →ᴬ[R] W) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ ↦ coe_smul _ _) fun _ _ ↦
    coe_smul _ _
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid S] [DistribMulAction S W] [SMulCommClass R S W] [ContinuousConstSMul S W] :
    DistribMulAction S (P →ᴬ[R] W) :=
  Function.Injective.distribMulAction ⟨⟨fun f ↦ f.toAffineMap.toFun, rfl⟩, coe_add⟩ coe_injective
    coe_smul
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring S] [Module S W] [SMulCommClass R S W] [ContinuousConstSMul S W] :
    Module S (P →ᴬ[R] W) :=
  Function.Injective.module S ⟨⟨fun f ↦ f.toAffineMap.toFun, rfl⟩, coe_add⟩ coe_injective coe_smul

variable [TopologicalSpace V] [IsTopologicalAddTorsor P]

@[simp]
/-
**ContinuousAffineMap.zero_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffin
eMap`。
形式化陈述：zero_contLinear : (0 : P ->ᴬ[R] W).contLinear = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
-/
theorem zero_contLinear : (0 : P →ᴬ[R] W).contLinear = 0 :=
  rfl

@[simp]
/-
**ContinuousAffineMap.add_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffine
Map`。
形式化陈述：add_contLinear (f g : P ->ᴬ[R] W) : (f + g).contLinear = f.contLinear + g.
contLinear
参数：f g : P ->ᴬ[R] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
-/
theorem add_contLinear (f g : P →ᴬ[R] W) : (f + g).contLinear = f.contLinear + g.contLinear :=
  rfl

@[simp]
/-
**ContinuousAffineMap.sub_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffine
Map`。
形式化陈述：sub_contLinear (f g : P ->ᴬ[R] W) : (f - g).contLinear = f.contLinear - g.
contLinear
参数：f g : P ->ᴬ[R] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
-/
theorem sub_contLinear (f g : P →ᴬ[R] W) : (f - g).contLinear = f.contLinear - g.contLinear :=
  rfl

@[simp]
/-
**ContinuousAffineMap.neg_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffine
Map`。
形式化陈述：neg_contLinear (f : P ->ᴬ[R] W) : (-f).contLinear = -f.contLinear
参数：f : P ->ᴬ[R] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
-/
theorem neg_contLinear (f : P →ᴬ[R] W) : (-f).contLinear = -f.contLinear :=
  rfl

end ModuleValuedMaps

section

variable [TopologicalSpace W] [IsTopologicalAddGroup W] [IsTopologicalAddTorsor Q]

/-- The space of continuous affine maps from `P` to `Q` is an affine space over the space of
continuous affine maps from `P` to `W`. -/
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of continuous affine maps from `P` to `Q` is an affine space over the 
space of
continuous affine maps from `P` to `W`.
-/
instance : AddTorsor (P →ᴬ[R] W) (P →ᴬ[R] Q) where
  vadd f g := { __ := f.toAffineMap +ᵥ g.toAffineMap, cont := f.cont.vadd g.cont }
  zero_vadd _ := ext fun _ ↦ zero_vadd _ _
  add_vadd _ _ _ := ext fun _ ↦ add_vadd _ _ _
  vsub f g := { __ := f.toAffineMap -ᵥ g.toAffineMap, cont := f.cont.vsub g.cont }
  vsub_vadd' _ _ := ext fun _ ↦ vsub_vadd _ _
  vadd_vsub' _ _ := ext fun _ ↦ vadd_vsub _ _
/-
**ContinuousAffineMap.vadd_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`
。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {W : Type u_3} {P : Type u_4} {Q : Type u_
5} [inst : Ring R] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module R V] [ins
t_3 : TopologicalSpace P] [inst_4 : AddTorsor V P] [inst_5 : AddCommGroup W]   [
inst_6 : _root_.Module R W] [inst_7 : TopologicalSpace Q] [inst_8 : AddTorsor W 
Q] [inst_9 : TopologicalSpace W]   [inst_10 : IsTopologicalAddGroup W] [inst_11 
: IsTopologicalAddTorsor Q] (f : P →ᴬ[R] W) (g : P →ᴬ[R] Q) (p : P),   (f +ᵥ g) 
p = f p +ᵥ g p
参数：f : P →ᴬ[R] W；g : P →ᴬ[R] Q；p : P；f +ᵥ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma vadd_apply (f : P →ᴬ[R] W) (g : P →ᴬ[R] Q) (p : P) : (f +ᵥ g) p = f p +ᵥ g p :=
  rfl
/-
**ContinuousAffineMap.vsub_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`
。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {W : Type u_3} {P : Type u_4} {Q : Type u_
5} [inst : Ring R] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module R V] [ins
t_3 : TopologicalSpace P] [inst_4 : AddTorsor V P] [inst_5 : AddCommGroup W]   [
inst_6 : _root_.Module R W] [inst_7 : TopologicalSpace Q] [inst_8 : AddTorsor W 
Q] [inst_9 : TopologicalSpace W]   [inst_10 : IsTopologicalAddGroup W] [inst_11 
: IsTopologicalAddTorsor Q] (f g : P →ᴬ[R] Q) (p : P),   (f -ᵥ g) p = f p -ᵥ g p
参数：f g : P →ᴬ[R] Q；p : P；f -ᵥ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma vsub_apply (f g : P →ᴬ[R] Q) (p : P) : (f -ᵥ g) p = f p -ᵥ g p :=
  rfl
/-
**ContinuousAffineMap.vadd_toAffineMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffi
neMap`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {W : Type u_3} {P : Type u_4} {Q : Type u_
5} [inst : Ring R] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module R V] [ins
t_3 : TopologicalSpace P] [inst_4 : AddTorsor V P] [inst_5 : AddCommGroup W]   [
inst_6 : _root_.Module R W] [inst_7 : TopologicalSpace Q] [inst_8 : AddTorsor W 
Q] [inst_9 : TopologicalSpace W]   [inst_10 : IsTopologicalAddGroup W] [inst_11 
: IsTopologicalAddTorsor Q] (f : P →ᴬ[R] W) (g : P →ᴬ[R] Q),   ↑(f +ᵥ g) = ↑f +ᵥ
 ↑g
参数：f : P →ᴬ[R] W；g : P →ᴬ[R] Q；f +ᵥ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma vadd_toAffineMap (f : P →ᴬ[R] W) (g : P →ᴬ[R] Q) :
    (f +ᵥ g).toAffineMap = f.toAffineMap +ᵥ g.toAffineMap :=
  rfl
/-
**ContinuousAffineMap.vsub_toAffineMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffi
neMap`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {W : Type u_3} {P : Type u_4} {Q : Type u_
5} [inst : Ring R] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module R V] [ins
t_3 : TopologicalSpace P] [inst_4 : AddTorsor V P] [inst_5 : AddCommGroup W]   [
inst_6 : _root_.Module R W] [inst_7 : TopologicalSpace Q] [inst_8 : AddTorsor W 
Q] [inst_9 : TopologicalSpace W]   [inst_10 : IsTopologicalAddGroup W] [inst_11 
: IsTopologicalAddTorsor Q] (f g : P →ᴬ[R] Q), ↑(f -ᵥ g) = ↑f -ᵥ ↑g
参数：f g : P →ᴬ[R] Q；f -ᵥ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma vsub_toAffineMap (f g : P →ᴬ[R] Q) :
    (f -ᵥ g).toAffineMap = f.toAffineMap -ᵥ g.toAffineMap :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Interpolating between `ContinuousAffineMap`s with `AffineMap.lineMap` commutes with
evaluation. -/
@[simp]
/-
**ContinuousAffineMap.lineMap_apply'** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousAffine
Map`。
形式化陈述：lineMap_apply' [ContinuousConstSMul R W] [SMulCommClass R R W] (f g : P ->
ᴬ[R] Q) (c : R) (p : P) : AffineMap.lineMap f g c p = AffineMap.lineMap (f p) (g
 p) c
参数：f g : P ->ᴬ[R] Q；c : R；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Interpolating between `ContinuousAffineMap`s with `AffineMap.lineMap` commutes w
ith
evaluation.
-/
lemma lineMap_apply' [ContinuousConstSMul R W] [SMulCommClass R R W] (f g : P →ᴬ[R] Q) (c : R)
    (p : P) : AffineMap.lineMap f g c p = AffineMap.lineMap (f p) (g p) c := by
  simp [AffineMap.lineMap_apply]

variable [TopologicalSpace V] [IsTopologicalAddTorsor P]
/-
**ContinuousAffineMap.vadd_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffin
eMap`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {W : Type u_3} {P : Type u_4} {Q : Type u_
5} [inst : Ring R] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module R V] [ins
t_3 : TopologicalSpace P] [inst_4 : AddTorsor V P] [inst_5 : AddCommGroup W]   [
inst_6 : _root_.Module R W] [inst_7 : TopologicalSpace Q] [inst_8 : AddTorsor W 
Q] [inst_9 : TopologicalSpace W]   [inst_10 : IsTopologicalAddGroup W] [inst_11 
: IsTopologicalAddTorsor Q] [inst_12 : TopologicalSpace V]   [inst_13 : IsTopolo
gicalAddTorsor P] (f : P →ᴬ[R] W) (g : P →ᴬ[R] Q),   (f +ᵥ g).contLinear = f.con
tLinear + g.contLinear
参数：f : P →ᴬ[R] W；g : P →ᴬ[R] Q；f +ᵥ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma vadd_contLinear (f : P →ᴬ[R] W) (g : P →ᴬ[R] Q) :
    (f +ᵥ g).contLinear = f.contLinear + g.contLinear :=
  rfl
/-
**ContinuousAffineMap.vsub_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffin
eMap`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {W : Type u_3} {P : Type u_4} {Q : Type u_
5} [inst : Ring R] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module R V] [ins
t_3 : TopologicalSpace P] [inst_4 : AddTorsor V P] [inst_5 : AddCommGroup W]   [
inst_6 : _root_.Module R W] [inst_7 : TopologicalSpace Q] [inst_8 : AddTorsor W 
Q] [inst_9 : TopologicalSpace W]   [inst_10 : IsTopologicalAddGroup W] [inst_11 
: IsTopologicalAddTorsor Q] [inst_12 : TopologicalSpace V]   [inst_13 : IsTopolo
gicalAddTorsor P] (f g : P →ᴬ[R] Q), (f -ᵥ g).contLinear = f.contLinear - g.cont
Linear
参数：f g : P →ᴬ[R] Q；f -ᵥ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
-/
@[simp] lemma vsub_contLinear (f g : P →ᴬ[R] Q) :
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
/-
**ContinuousAffineMap.prod** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineMap`。
形式化陈述：prod (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃) : P₁ ->ᴬ[k] P₂ × P₃ where __
参数：f : P₁ ->ᴬ[k] P₂；g : P₁ ->ᴬ[k] P₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two continuous affine maps is a continuous affine map.
-/
def prod (f : P₁ →ᴬ[k] P₂) (g : P₁ →ᴬ[k] P₃) : P₁ →ᴬ[k] P₂ × P₃ where
  __ := AffineMap.prod f g
  cont := by eta_expand; dsimp; fun_prop
/-
**ContinuousAffineMap.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：coe_prod (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃) : prod f g = Function.prod 
f g
参数：f : P₁ ->ᴬ[k] P₂；g : P₁ ->ᴬ[k] P₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (f : P₁ →ᴬ[k] P₂) (g : P₁ →ᴬ[k] P₃) : prod f g = Function.prod f g :=
  rfl

@[simp]
/-
**ContinuousAffineMap.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`
。
形式化陈述：prod_apply (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃) (p : P₁) : prod f g p = (
f p, g p)
参数：f : P₁ ->ᴬ[k] P₂；g : P₁ ->ᴬ[k] P₃；p : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_apply (f : P₁ →ᴬ[k] P₂) (g : P₁ →ᴬ[k] P₃) (p : P₁) : prod f g p = (f p, g p) :=
  rfl

/-- `Prod.map` of two continuous affine maps. -/
@[simps toAffineMap]
/-
**ContinuousAffineMap.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineMap`。
形式化陈述：prodMap (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄) : P₁ × P₃ ->ᴬ[k] P₂ × P₄ whe
re __
参数：f : P₁ ->ᴬ[k] P₂；g : P₃ ->ᴬ[k] P₄。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.map` of two continuous affine maps.
-/
def prodMap (f : P₁ →ᴬ[k] P₂) (g : P₃ →ᴬ[k] P₄) : P₁ × P₃ →ᴬ[k] P₂ × P₄ where
  __ := AffineMap.prodMap f g
  cont := by eta_expand; dsimp; fun_prop
/-
**ContinuousAffineMap.coe_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap
`。
形式化陈述：coe_prodMap (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄) : ⇑(f.prodMap g) = Prod.
map f g
参数：f : P₁ ->ᴬ[k] P₂；g : P₃ ->ᴬ[k] P₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodMap (f : P₁ →ᴬ[k] P₂) (g : P₃ →ᴬ[k] P₄) : ⇑(f.prodMap g) = Prod.map f g :=
  rfl

@[simp]
/-
**ContinuousAffineMap.prodMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineM
ap`。
形式化陈述：prodMap_apply (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄) (x) : f.prodMap g x = 
(f x.1, g x.2)
参数：f : P₁ ->ᴬ[k] P₂；g : P₃ ->ᴬ[k] P₄；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_apply (f : P₁ →ᴬ[k] P₂) (g : P₃ →ᴬ[k] P₄) (x) : f.prodMap g x = (f x.1, g x.2) :=
  rfl

variable
  [TopologicalSpace V₁] [IsTopologicalAddTorsor P₁]
  [TopologicalSpace V₂] [IsTopologicalAddTorsor P₂]
  [TopologicalSpace V₃] [IsTopologicalAddTorsor P₃]
  [TopologicalSpace V₄] [IsTopologicalAddTorsor P₄]

@[simp]
/-
**ContinuousAffineMap.prod_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffin
eMap`。
形式化陈述：prod_contLinear (f : P₁ ->ᴬ[k] P₂) (g : P₁ ->ᴬ[k] P₃) : (f.prod g).contLin
ear = f.contLinear.prod g.contLinear
参数：f : P₁ ->ᴬ[k] P₂；g : P₁ ->ᴬ[k] P₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsorProd`：∀ {V : Type u_1} {W : Type u_2} {P : Typ
e u_3} {Q : Type u_4} [inst : AddCommGroup V] [inst_1 : TopologicalSpace V]   [i
nst_2 : AddTorsor V …
-/
theorem prod_contLinear (f : P₁ →ᴬ[k] P₂) (g : P₁ →ᴬ[k] P₃) :
    (f.prod g).contLinear = f.contLinear.prod g.contLinear :=
  rfl

@[simp]
/-
**ContinuousAffineMap.prodMap_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAf
fineMap`。
形式化陈述：prodMap_contLinear (f : P₁ ->ᴬ[k] P₂) (g : P₃ ->ᴬ[k] P₄) : (f.prodMap g).c
ontLinear = f.contLinear.prodMap g.contLinear
参数：f : P₁ ->ᴬ[k] P₂；g : P₃ ->ᴬ[k] P₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsorProd`：∀ {V : Type u_1} {W : Type u_2} {P : Typ
e u_3} {Q : Type u_4} [inst : AddCommGroup V] [inst_1 : TopologicalSpace V]   [i
nst_2 : AddTorsor V …
-/
theorem prodMap_contLinear (f : P₁ →ᴬ[k] P₂) (g : P₃ →ᴬ[k] P₄) :
    (f.prodMap g).contLinear = f.contLinear.prodMap g.contLinear :=
  rfl

end Prod

end ContinuousAffineMap

namespace ContinuousLinearMap

variable {R V W : Type*} [Ring R]
variable [AddCommGroup V] [Module R V] [TopologicalSpace V]
variable [AddCommGroup W] [Module R W] [TopologicalSpace W]

/-- A continuous linear map can be regarded as a continuous affine map. -/
/-
**ContinuousLinearMap.toContinuousAffineMap** 是 Mathlib 中的一个定义，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：toContinuousAffineMap (f : V ->L[R] W) : V ->ᴬ[R] W where toFun
参数：f : V ->L[R] W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear map can be regarded as a continuous affine map.
-/
def toContinuousAffineMap (f : V →L[R] W) : V →ᴬ[R] W where
  toFun := f
  linear := f
  map_vadd' := by simp
  cont := f.cont

@[simp]
/-
**ContinuousLinearMap.coe_toContinuousAffineMap** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearMap`。
形式化陈述：coe_toContinuousAffineMap (f : V ->L[R] W) : ⇑f.toContinuousAffineMap = f
参数：f : V ->L[R] W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousAffineMap (f : V →L[R] W) : ⇑f.toContinuousAffineMap = f := rfl

@[simp]
/-
**ContinuousLinearMap.toContinuousAffineMap_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap`。
形式化陈述：toContinuousAffineMap_map_zero (f : V ->L[R] W) : f.toContinuousAffineMap 
0 = 0
参数：f : V ->L[R] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toContinuousAffineMap_map_zero (f : V →L[R] W) : f.toContinuousAffineMap 0 = 0 := by simp

variable [IsTopologicalAddGroup V] [IsTopologicalAddGroup W]

@[simp]
/-
**ContinuousLinearMap.toContinuousAffineMap_contLinear** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousLinearMap`。
形式化陈述：toContinuousAffineMap_contLinear (f : V ->L[R] W) : f.toContinuousAffineMa
p.contLinear = f
参数：f : V ->L[R] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
-/
theorem toContinuousAffineMap_contLinear (f : V →L[R] W) : f.toContinuousAffineMap.contLinear = f :=
  rfl
/-
**ContinuousLinearMap._root_.ContinuousAffineMap.decomp** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousAffineMap.decomp (f : V →ᴬ[R] W) :
    (f : V → W) = f.contLinear + Function.const V (f 0) := by
  rcases f with ⟨f, h⟩
  rw [ContinuousAffineMap.coe_mk_contLinear_eq_linear, ContinuousAffineMap.coe_mk, f.decomp,
    Pi.add_apply, LinearMap.map_zero, zero_add, ← Function.const_def]

end ContinuousLinearMap

namespace ContinuousAffineMap

variable (R S V : Type*) {W : Type*} (Q : Type*) [Ring S] [Ring R]
variable [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [AddCommGroup W] [Module R W] [TopologicalSpace W]
variable [Module S W] [SMulCommClass R S W] [ContinuousConstSMul S W]
variable [AddTorsor W Q] [TopologicalSpace Q]

section

variable [IsTopologicalAddTorsor Q]

/-- The space of continuous affine maps from a topological vector space to a topological affine
space is in bijection with the product of the codomain with the space of linear maps, by taking the
value of the affine map at `(0 : V)` and the linear part. -/
/-
**ContinuousAffineMap.decompEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineMap
`。
形式化陈述：decompEquiv : (V ->ᴬ[R] Q) ≃ Q × (V ->L[R] W) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of continuous affine maps from a topological vector space to a topolog
ical affine
space is in bijection with the product of the codomain with the space of linear 
maps, by taking the
value of the affine map at `(0 : V)` and the linear part.
-/
def decompEquiv : (V →ᴬ[R] Q) ≃ Q × (V →L[R] W) where
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
/-
**ContinuousAffineMap.fst_decompEquiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffin
eMap`。
形式化陈述：fst_decompEquiv (f : V ->ᴬ[R] Q) : (decompEquiv R V Q f).1 = f 0
参数：f : V ->ᴬ[R] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_decompEquiv (f : V →ᴬ[R] Q) :
    (decompEquiv R V Q f).1 = f 0 :=
  rfl

@[simp]
/-
**ContinuousAffineMap.snd_decompEquiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffin
eMap`。
形式化陈述：snd_decompEquiv (f : V ->ᴬ[R] Q) : (decompEquiv R V Q f).2 = f.contLinear
参数：f : V ->ᴬ[R] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_decompEquiv (f : V →ᴬ[R] Q) :
    (decompEquiv R V Q f).2 = f.contLinear :=
  rfl

@[simp]
/-
**ContinuousAffineMap.decompEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usAffineMap`。
形式化陈述：decompEquiv_symm_apply (p : Q × (V ->L[R] W)) (x : V) : (decompEquiv R V Q
).symm p x = p.2 x +ᵥ p.1
参数：p : Q × (V ->L[R] W)；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem decompEquiv_symm_apply (p : Q × (V →L[R] W)) (x : V) :
    (decompEquiv R V Q).symm p x = p.2 x +ᵥ p.1 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ContinuousAffineMap.decompEquiv_symm_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousAffineMap`。
形式化陈述：decompEquiv_symm_contLinear (p : Q × (V ->L[R] W)) : ((decompEquiv R V Q).
symm p).contLinear = p.2
参数：p : Q × (V ->L[R] W)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddTorsor.to_isTopologicalAddGroup`：∀ (V : Type u_1) (P : T
ype u_2) [inst : AddGroup V] [inst_1 : TopologicalSpace V] [inst_2 : AddTorsor V
 P]   [inst_3 : TopologicalSpace P] […
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem decompEquiv_symm_contLinear (p : Q × (V →L[R] W)) :
    ((decompEquiv R V Q).symm p).contLinear = p.2 := by
  have := IsTopologicalAddTorsor.to_isTopologicalAddGroup W Q
  ext; simp [decompEquiv]

end

section

variable (W) [IsTopologicalAddGroup W]

/-- The space of continuous affine maps between topological vector spaces is linearly isomorphic to
the product of the codomain with the space of linear maps, by taking the value of the affine map at
`(0 : V)` and the linear part. -/
/-
**ContinuousAffineMap.decompLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAff
ineMap`。
形式化陈述：decompLinearEquiv : (V ->ᴬ[R] W) ≃ₗ[S] W × (V ->L[R] W) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of continuous affine maps between topological vector spaces is linearl
y isomorphic to
the product of the codomain with the space of linear maps, by taking the value o
f the affine map at
`(0 : V)` and the linear part.
-/
def decompLinearEquiv : (V →ᴬ[R] W) ≃ₗ[S] W × (V →L[R] W) where
  __ := decompEquiv R V W
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/-
**ContinuousAffineMap.fst_decompLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sAffineMap`。
形式化陈述：fst_decompLinearEquiv (f : V ->ᴬ[R] W) : (decompLinearEquiv R S V W f).1 =
 f 0
参数：f : V ->ᴬ[R] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem fst_decompLinearEquiv (f : V →ᴬ[R] W) :
    (decompLinearEquiv R S V W f).1 = f 0 :=
  rfl

@[simp]
/-
**ContinuousAffineMap.snd_decompLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sAffineMap`。
形式化陈述：snd_decompLinearEquiv (f : V ->ᴬ[R] W) : (decompLinearEquiv R S V W f).2 =
 f.contLinear
参数：f : V ->ᴬ[R] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem snd_decompLinearEquiv (f : V →ᴬ[R] W) :
    (decompLinearEquiv R S V W f).2 = f.contLinear :=
  rfl

@[simp]
/-
**ContinuousAffineMap.decompLinearEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousAffineMap`。
形式化陈述：decompLinearEquiv_symm_apply (p : W × (V ->L[R] W)) (x : V) : (decompLinea
rEquiv R S V W).symm p x = p.2 x + p.1
参数：p : W × (V ->L[R] W)；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem decompLinearEquiv_symm_apply (p : W × (V →L[R] W)) (x : V) :
    (decompLinearEquiv R S V W).symm p x = p.2 x + p.1 :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ContinuousAffineMap.decompLinearEquiv_symm_contLinear** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousAffineMap`。
形式化陈述：decompLinearEquiv_symm_contLinear (p : W × (V ->L[R] W)) : ((decompLinearE
quiv R S V W).symm p).contLinear = p.2
参数：p : W × (V ->L[R] W)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAffineMap.decompEquiv_symm_contLinear`：decompEquiv_symm_contLi
near (p : Q × (V ->L[R] W)) : ((decompEquiv R V Q).symm p).contLinear = p.2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem decompLinearEquiv_symm_contLinear (p : W × (V →L[R] W)) :
    ((decompLinearEquiv R S V W).symm p).contLinear = p.2 := by
  ext; simp [decompLinearEquiv]

end

section

variable [IsTopologicalAddGroup W] [IsTopologicalAddTorsor Q]

/-- The space of continuous affine maps from a topological vector space to a topological affine
space is affinely isomorphic to the product of the codomain with the space of linear maps, by taking
the value of the affine map at `(0 : V)` and the linear part. -/
@[simps linear]
/-
**ContinuousAffineMap.decompAffineEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAff
ineMap`。
形式化陈述：decompAffineEquiv : (V ->ᴬ[R] Q) ≃ᵃ[S] Q × (V ->L[R] W) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of continuous affine maps from a topological vector space to a topolog
ical affine
space is affinely isomorphic to the product of the codomain with the space of li
near maps, by taking
the value of the affine map at `(0 : V)` and the linear part.
-/
def decompAffineEquiv : (V →ᴬ[R] Q) ≃ᵃ[S] Q × (V →L[R] W) where
  __ := decompEquiv R V Q
  linear := decompLinearEquiv R S V W
  map_vadd' _ _ := rfl

@[simp]
/-
**ContinuousAffineMap.fst_decompAffineEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sAffineMap`。
形式化陈述：fst_decompAffineEquiv (f : V ->ᴬ[R] Q) : (decompAffineEquiv R S V Q f).1 =
 f 0
参数：f : V ->ᴬ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem fst_decompAffineEquiv (f : V →ᴬ[R] Q) :
    (decompAffineEquiv R S V Q f).1 = f 0 :=
  rfl

@[simp]
/-
**ContinuousAffineMap.snd_decompAffineEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sAffineMap`。
形式化陈述：snd_decompAffineEquiv (f : V ->ᴬ[R] Q) : (decompAffineEquiv R S V Q f).2 =
 f.contLinear
参数：f : V ->ᴬ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem snd_decompAffineEquiv (f : V →ᴬ[R] Q) :
    (decompAffineEquiv R S V Q f).2 = f.contLinear :=
  rfl

@[simp]
/-
**ContinuousAffineMap.decompAffineEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousAffineMap`。
形式化陈述：decompAffineEquiv_symm_apply (p : Q × (V ->L[R] W)) (x : V) : (decompAffin
eEquiv R S V Q).symm p x = p.2 x +ᵥ p.1
参数：p : Q × (V ->L[R] W)；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem decompAffineEquiv_symm_apply (p : Q × (V →L[R] W)) (x : V) :
    (decompAffineEquiv R S V Q).symm p x = p.2 x +ᵥ p.1 :=
  rfl

@[simp]
/-
**ContinuousAffineMap.decompAffineEquiv_symm_contLinear** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousAffineMap`。
形式化陈述：decompAffineEquiv_symm_contLinear (p : Q × (V ->L[R] W)) : ((decompAffineE
quiv R S V Q).symm p).contLinear = p.2
参数：p : Q × (V ->L[R] W)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAffineMap.decompAffineEquiv.eq_1`：∀ (R : Type u_1) (S : Type u
_2) (V : Type u_3) {W : Type u_4} (Q : Type u_5) [inst : Ring S] [inst_1 : Ring 
R]   [inst_2 : AddCommGroup V] […
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineEquiv.coe_symm_toEquiv`：coe_symm_toEquiv (e : P₁ ≃ᵃ[k] P₂) : ⇑e.to
Equiv.symm = e.symm
· 使用定理 `ContinuousAffineMap.decompEquiv_symm_contLinear`：decompEquiv_symm_contLi
near (p : Q × (V ->L[R] W)) : ((decompEquiv R V Q).symm p).contLinear = p.2
-/
theorem decompAffineEquiv_symm_contLinear (p : Q × (V →L[R] W)) :
    ((decompAffineEquiv R S V Q).symm p).contLinear = p.2 := by
  rw [decompAffineEquiv, ← AffineEquiv.coe_symm_toEquiv, decompEquiv_symm_contLinear]

end

end ContinuousAffineMap

