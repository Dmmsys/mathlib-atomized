/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Restrict
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Topology of affine subspaces.

This file defines the embedding map from an affine subspace to the ambient space as a continuous
affine map.

## Main definitions

* `AffineSubspace.subtypeA` is `AffineSubspace.subtype` as a `ContinuousAffineMap`.

-/

@[expose] public section


namespace AffineSubspace

variable {R V P : Type*} [Ring R] [AddCommGroup V] [Module R V] [TopologicalSpace P]
  [AddTorsor V P]

/-- Embedding of an affine subspace to the ambient space, as a continuous affine map. -/
/-
**AffineSubspace.subtypeA** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：subtypeA (s : AffineSubspace R P) [Nonempty s] : s ->ᴬ[R] P where toAffine
Map
参数：s : AffineSubspace R P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of an affine subspace to the ambient space, as a continuous affine map
.
-/
def subtypeA (s : AffineSubspace R P) [Nonempty s] : s →ᴬ[R] P where
  toAffineMap := s.subtype
  cont := continuous_subtype_val
/-
**AffineSubspace.coe_subtypeA** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring R] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module R V]   [inst_3 : TopologicalSpace P] [ins
t_4 : AddTorsor V P] (s : AffineSubspace R P) [inst_5 : Nonempty ↥s],   ⇑s.subty
peA = Subtype.val
参数：s : AffineSubspace R P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_subtypeA (s : AffineSubspace R P) [Nonempty s] : ⇑s.subtypeA = Subtype.val :=
  rfl
/-
**AffineSubspace.subtypeA_toAffineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`
。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring R] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module R V]   [inst_3 : TopologicalSpace P] [ins
t_4 : AddTorsor V P] (s : AffineSubspace R P) [inst_5 : Nonempty ↥s],   ↑s.subty
peA = s.subtype
参数：s : AffineSubspace R P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma subtypeA_toAffineMap (s : AffineSubspace R P) [Nonempty s] :
    s.subtypeA.toAffineMap = s.subtype :=
  rfl

/-- `AffineEquiv.ofEq` as a continuous affine equivalence. -/
/-
**AffineSubspace.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：ofEq {s t : AffineSubspace R P} [Nonempty s] [Nonempty t] (h : s = t) : s 
≃ᴬ[R] t where toAffineEquiv
参数：h : s = t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AffineEquiv.ofEq` as a continuous affine equivalence.
-/
noncomputable def ofEq {s t : AffineSubspace R P} [Nonempty s] [Nonempty t]
    (h : s = t) : s ≃ᴬ[R] t where
  toAffineEquiv := .ofEq s t h
  continuous_toFun := by subst h; exact continuous_id
  continuous_invFun := by subst h; exact continuous_id

@[simp]
/-
**AffineSubspace.coe_ofEq_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_ofEq_apply {s t : AffineSubspace R P} [Nonempty s] [Nonempty t] (h : s
 = t) (x : s) : (ofEq h x : P) = x
参数：h : s = t；x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.coe_ofEq_apply`：coe_ofEq_apply (h : S₁ = S₂) (x : S₁) : (ofE
q S₁ S₂ h x : P₁) = x
-/
theorem coe_ofEq_apply {s t : AffineSubspace R P} [Nonempty s] [Nonempty t]
    (h : s = t) (x : s) : (ofEq h x : P) = x := AffineEquiv.coe_ofEq_apply s t h x

end AffineSubspace

namespace ContinuousAffineEquiv

variable {R V P W Q : Type*} [Ring R] [AddCommGroup V] [Module R V] [TopologicalSpace P]
  [AddTorsor V P] [AddCommGroup W] [Module R W] [TopologicalSpace Q] [AddTorsor W Q]

/-- A continuous affine equivalence restricts to a continuous affine equivalence between an affine
subspace and its image.

This is the continuous affine version of `AffineEquiv.affineSubspaceMap`. -/
/-
**ContinuousAffineEquiv.affineSubspaceMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousA
ffineEquiv`。
形式化陈述：affineSubspaceMap (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P) [Nonempty s] : 
s ≃ᴬ[R] s.map e.toAffineMap
参数：e : P ≃ᴬ[R] Q；s : AffineSubspace R P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous affine equivalence restricts to a continuous affine equivalence bet
ween an affine
subspace and its image.

This is the continuous affine version of `AffineEquiv.affineSubspaceMap`.
-/
noncomputable def affineSubspaceMap (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P) [Nonempty s] :
    s ≃ᴬ[R] s.map e.toAffineMap :=
  { e.toAffineEquiv.affineSubspaceMap s with
    continuous_toFun := by simpa [Topology.IsEmbedding.subtypeVal.continuous_iff] using!
      (e.continuous.comp continuous_subtype_val).congr fun _ => rfl
    continuous_invFun := by simpa [Topology.IsEmbedding.subtypeVal.continuous_iff] using!
      (e.continuous_invFun.comp continuous_subtype_val).congr fun x ↦
        (e.eq_symm_apply.mpr
          (AffineEquiv.affineSubspaceMap_apply_symm_apply e.toAffineEquiv s x)).symm }

@[simp]
/-
**ContinuousAffineEquiv.affineSubspaceMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousAffineEquiv`。
形式化陈述：affineSubspaceMap_apply (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P) [Nonempty
 s] (x : s) : e.affineSubspaceMap s x = e x
参数：e : P ≃ᴬ[R] Q；s : AffineSubspace R P；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem affineSubspaceMap_apply (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P) [Nonempty s]
    (x : s) : e.affineSubspaceMap s x = e x := rfl

@[simp]
/-
**ContinuousAffineEquiv.affineSubspaceMap_apply_symm_apply** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousAffineEquiv`。
形式化陈述：affineSubspaceMap_apply_symm_apply (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P
) [Nonempty s] (x : s.map e.toAffineMap) : e ((e.affineSubspaceMap s).symm x) = 
x
参数：e : P ≃ᴬ[R] Q；s : AffineSubspace R P；x : s.map e.toAffineMap。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.affineSubspaceMap_apply_symm_apply`：affineSubspaceMap_apply_
symm_apply (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁) [Nonempty s] (x : s.map e
.toAffineMap) : e ((e.affineSubspace…
-/
theorem affineSubspaceMap_apply_symm_apply (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P)
    [Nonempty s] (x : s.map e.toAffineMap) : e ((e.affineSubspaceMap s).symm x) = x :=
  AffineEquiv.affineSubspaceMap_apply_symm_apply e.toAffineEquiv s x

end ContinuousAffineEquiv

namespace AffineSubspace

variable {R V P : Type*} [Ring R] [AddCommGroup V] [Module R V] [TopologicalSpace P]
  [AddTorsor V P]

variable [TopologicalSpace V] [IsTopologicalAddTorsor P]

/-
**AffineSubspace.** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {s : AffineSubspace R P} [Nonempty s] : IsTopologicalAddTorsor s where
  continuous_vadd := by
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    fun_prop
  continuous_vsub := by
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    fun_prop

set_option backward.isDefEq.respectTransparency false in
/-
**AffineSubspace.isClosed_direction_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e`。
形式化陈述：isClosed_direction_iff [T1Space V] (s : AffineSubspace R P) : IsClosed (s.
direction : Set V) ↔ IsClosed (s : Set P)
参数：s : AffineSubspace R P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.eq_bot_or_nonempty`：eq_bot_or_nonempty (Q : AffineSubspac
e k P) : Q = ⊥ ∨ (Q : Set P).Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.direction_bot`：direction_bot : (⊥ : AffineSubspace k P).d
irection = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.isClosed_image`：isClosed_image (h : X ≃ₜ Y) {s : Set X} : IsC
losed (h '' s) ↔ IsClosed s
· 使用定理 `AffineSubspace.coe_direction_eq_vsub_set_right`：coe_direction_eq_vsub_se
t_right {s : AffineSubspace k P} {p : P} (hp : p in s) : (s.direction : Set V) =
 (· -ᵥ p) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Homeomorph.vaddConst_symm_apply`：∀ {V : Type u_1} {P : Type u_2} [inst :
 AddGroup V] [inst_1 : TopologicalSpace V] [inst_2 : AddTorsor V P]   [inst_3 : 
TopologicalSpace P] […
-/
theorem isClosed_direction_iff [T1Space V] (s : AffineSubspace R P) :
    IsClosed (s.direction : Set V) ↔ IsClosed (s : Set P) := by
  rcases s.eq_bot_or_nonempty with (rfl | ⟨x, hx⟩); · simp
  rw [← (Homeomorph.vaddConst x).symm.isClosed_image,
    AffineSubspace.coe_direction_eq_vsub_set_right hx]
  simp only [Homeomorph.vaddConst_symm_apply]

end AffineSubspace

