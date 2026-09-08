/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Orthogonal projection in affine spaces

This file defines orthogonal projection onto an affine subspace,
and reflection of a point in an affine subspace.

## Main definitions

* `EuclideanGeometry.orthogonalProjection` is the orthogonal
  projection of a point onto an affine subspace.

* `EuclideanGeometry.reflection` is the reflection of a point in an
  affine subspace.

-/

@[expose] public section

noncomputable section

namespace EuclideanGeometry

variable {𝕜 : Type*} {V : Type*} {P : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace 𝕜 V₂]

open AffineSubspace

variable [MetricSpace P] [NormedAddTorsor V P]

/-- The orthogonal projection of a point onto a nonempty affine subspace. -/
/-
**EuclideanGeometry.orthogonalProjection** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGeo
metry`。
形式化陈述：orthogonalProjection (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.Ha
sOrthogonalProjection] : P ->ᴬ[𝕜] s
参数：s : AffineSubspace 𝕜 P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthogonal projection of a point onto a nonempty affine subspace.
-/
def orthogonalProjection (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] : P →ᴬ[𝕜] s :=
  letI x := Classical.arbitrary s
  AffineIsometryEquiv.vaddConst 𝕜 x
    |>.toContinuousAffineEquiv.toContinuousAffineMap.comp
      s.direction.orthogonalProjectionOnto.toContinuousAffineMap
    |>.comp <| AffineIsometryEquiv.vaddConst 𝕜 (x : P) |>.symm
/-
**EuclideanGeometry.orthogonalProjection_apply** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
形式化陈述：orthogonalProjection_apply (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direct
ion.HasOrthogonalProjection] {p} : orthogonalProjection s p = s.direction.orthog
onalProjectionOnto (p -ᵥ Classical.arbitrary s) +ᵥ Classical.arbitrary s
参数：s : AffineSubspace 𝕜 P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orthogonalProjection_apply (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p} :
    orthogonalProjection s p = s.direction.orthogonalProjectionOnto (p -ᵥ Classical.arbitrary s)
      +ᵥ Classical.arbitrary s :=
  rfl
/-
**EuclideanGeometry.orthogonalProjection_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Eucli
deanGeometry`。
形式化陈述：orthogonalProjection_apply' (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direc
tion.HasOrthogonalProjection] {p} : (orthogonalProjection s p : P) = (s.directio
n.orthogonalProjectionOnto (p -ᵥ Classical.arbitrary s) : V) +ᵥ (Classical.arbit
rary s : P)
参数：s : AffineSubspace 𝕜 P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orthogonalProjection_apply' (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p} :
    (orthogonalProjection s p : P) =
      (s.direction.orthogonalProjectionOnto (p -ᵥ Classical.arbitrary s) : V) +ᵥ
      (Classical.arbitrary s : P) :=
  rfl
/-
**EuclideanGeometry.orthogonalProjection_apply_mem** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry`。
形式化陈述：orthogonalProjection_apply_mem (s : AffineSubspace 𝕜 P) [Nonempty s] [s.di
rection.HasOrthogonalProjection] {p x} (hx : x in s) : orthogonalProjection s p 
= (s.direction.orthogonalProjectionOnto (p -ᵥ x) : V) +ᵥ x
参数：s : AffineSubspace 𝕜 P；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.orthogonalProjection_apply`：orthogonalProjection_apply
 (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] {p}
 : orthogonalProjection s p = s.di…
· 使用定理 `AffineSubspace.coe_vadd`：coe_vadd (s : AffineSubspace k P) [Nonempty s] 
(a : s.direction) (b : s) : ↑(a +ᵥ b) = (a : V) +ᵥ (b : P)
· 使用定理 `vadd_eq_vadd_iff_sub_eq_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : Ad
dCommGroup G] [inst_1 : AddTorsor G P] {v₁ v₂ : G} {p₁ p₂ : P},   v₁ +ᵥ p₁ = v₂ 
+ᵥ p₂ ↔ v₂ - v₁ = …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.coe_sub`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   (x y : ↥p)
, ↑(x -…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用引理 `Submodule.coe_orthogonalProjectionOnto_apply`：coe_orthogonalProjectionOn
to_apply (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (v : E) : U.orthogonalP
rojectionOnto v = U.starProjection…
· 使用定理 `Submodule.starProjection_eq_self_iff`：starProjection_eq_self_iff {v : E}
 : K.starProjection v = v ↔ v in K
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
-/
theorem orthogonalProjection_apply_mem (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p x} (hx : x ∈ s) :
    orthogonalProjection s p = (s.direction.orthogonalProjectionOnto (p -ᵥ x) : V) +ᵥ x := by
  rw [orthogonalProjection_apply, coe_vadd, vadd_eq_vadd_iff_sub_eq_vsub, ← Submodule.coe_sub,
    ← map_sub, vsub_sub_vsub_cancel_left, Submodule.coe_orthogonalProjectionOnto_apply,
    Submodule.starProjection_eq_self_iff]
  exact s.vsub_mem_direction (SetLike.coe_mem _) hx

/-- Since both instance arguments are propositions, allow `simp` to rewrite them
alongside the `s` argument.

Note that without the coercion to `P`, the LHS and RHS would have different types. -/
@[congr]
/-
**EuclideanGeometry.orthogonalProjection_congr** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
形式化陈述：orthogonalProjection_congr {s₁ s₂ : AffineSubspace 𝕜 P} {p₁ p₂ : P} [Nonem
pty s₁] [s₁.direction.HasOrthogonalProjection] (h : s₁ = s₂) (hp : p₁ = p₂) : le
tI : Nonempty s₂
参数：h : s₁ = s₂；hp : p₁ = p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Since both instance arguments are propositions, allow `simp` to rewrite them
alongside the `s` argument.

Note that without the coercion to `P`, the LHS and RHS would have different type
s.
-/
theorem orthogonalProjection_congr {s₁ s₂ : AffineSubspace 𝕜 P} {p₁ p₂ : P}
    [Nonempty s₁] [s₁.direction.HasOrthogonalProjection]
    (h : s₁ = s₂) (hp : p₁ = p₂) :
    letI : Nonempty s₂ := h ▸ ‹_›
    letI : s₂.direction.HasOrthogonalProjection := h ▸ ‹_›
    (orthogonalProjection s₁ p₁ : P) = (orthogonalProjection s₂ p₂ : P) := by
  subst h hp
  rfl

/-- The linear map corresponding to `orthogonalProjection`. -/
@[simp]
/-
**EuclideanGeometry.orthogonalProjection_linear** 是 Mathlib 中的一个定理，位于命名空间 `Eucli
deanGeometry`。
形式化陈述：orthogonalProjection_linear {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direc
tion.HasOrthogonalProjection] : (orthogonalProjection s).linear = s.direction.or
thogonalProjectionOnto
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map corresponding to `orthogonalProjection`.
-/
theorem orthogonalProjection_linear {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] :
    (orthogonalProjection s).linear = s.direction.orthogonalProjectionOnto :=
  rfl

/-- The continuous linear map corresponding to `orthogonalProjection`. -/
@[simp]
/-
**EuclideanGeometry.orthogonalProjection_contLinear** 是 Mathlib 中的一个定理，位于命名空间 `E
uclideanGeometry`。
形式化陈述：orthogonalProjection_contLinear {s : AffineSubspace 𝕜 P} [Nonempty s] [s.d
irection.HasOrthogonalProjection] : (orthogonalProjection s).contLinear = s.dire
ction.orthogonalProjectionOnto
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `AffineSubspace.instIsTopologicalAddTorsorSubtypeMemSubmoduleDirection`：∀
 {R : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring R] [inst_1 : AddCommG
roup V] [inst_2 : _root_.Module R V]   [inst_3 : Topologica…

--- 原说明 ---
The continuous linear map corresponding to `orthogonalProjection`.
-/
theorem orthogonalProjection_contLinear {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] :
    (orthogonalProjection s).contLinear = s.direction.orthogonalProjectionOnto :=
  rfl

/-- The `orthogonalProjection` lies in the given subspace. -/
/-
**EuclideanGeometry.orthogonalProjection_mem** 是 Mathlib 中的一个定理，位于命名空间 `Euclidea
nGeometry`。
形式化陈述：orthogonalProjection_mem {s : AffineSubspace 𝕜 P} [Nonempty s] [s.directio
n.HasOrthogonalProjection] (p : P) : ↑(orthogonalProjection s p) in s
参数：p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The `orthogonalProjection` lies in the given subspace.
-/
theorem orthogonalProjection_mem {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : ↑(orthogonalProjection s p) ∈ s :=
  (orthogonalProjection s p).2

/-- The `orthogonalProjection` lies in the orthogonal subspace. -/
/-
**EuclideanGeometry.orthogonalProjection_mem_orthogonal** 是 Mathlib 中的一个定理，位于命名空
间 `EuclideanGeometry`。
形式化陈述：orthogonalProjection_mem_orthogonal (s : AffineSubspace 𝕜 P) [Nonempty s] 
[s.direction.HasOrthogonalProjection] (p : P) : ↑(orthogonalProjection s p) in m
k' p s.directionᗮ
参数：s : AffineSubspace 𝕜 P；p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.mem_mk'`：mem_mk' {p q : P} {direction : Submodule k V} : 
q in mk' p direction ↔ q -ᵥ p in direction
· 使用定理 `EuclideanGeometry.orthogonalProjection_apply`：orthogonalProjection_apply
 (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] {p}
 : orthogonalProjection s p = s.di…
· 使用定理 `AffineSubspace.coe_vadd`：coe_vadd (s : AffineSubspace k P) [Nonempty s] 
(a : s.direction) (b : s) : ↑(a +ᵥ b) = (a : V) +ᵥ (b : P)
· 使用定理 `vadd_vsub_eq_sub_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (g : G) (p q : P), (g +ᵥ p) -ᵥ q = g - (q -ᵥ p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.neg_mem_iff`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst
_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M
}, -x ∈ p ↔…
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Submodule.sub_starProjection_mem_orthogonal`：sub_starProjection_mem_orth
ogonal (v : E) : v - K.starProjection v in Kᗮ

--- 原说明 ---
The `orthogonalProjection` lies in the orthogonal subspace.
-/
theorem orthogonalProjection_mem_orthogonal (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    ↑(orthogonalProjection s p) ∈ mk' p s.directionᗮ := by
  rw [mem_mk', orthogonalProjection_apply, coe_vadd, vadd_vsub_eq_sub_vsub,
    ← Submodule.neg_mem_iff, neg_sub]
  apply Submodule.sub_starProjection_mem_orthogonal

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonalProjection` of that point
onto the subspace. -/
/-
**EuclideanGeometry.inter_eq_singleton_orthogonalProjection** 是 Mathlib 中的一个定理，位
于命名空间 `EuclideanGeometry`。
形式化陈述：inter_eq_singleton_orthogonalProjection {s : AffineSubspace 𝕜 P} [Nonempty
 s] [s.direction.HasOrthogonalProjection] (p : P) : (s : Set P) inter mk' p s.di
rectionᗮ = {↑(orthogonalProjection s p)}
参数：p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.inter_eq_singleton_of_nonempty_of_isCompl`：inter_eq_singl
eton_of_nonempty_of_isCompl {s₁ s₂ : AffineSubspace k P} (h1 : (s₁ : Set P).None
mpty) (h2 : (s₂ : Set P).Nonempty) (hd : IsCom…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `AffineSubspace.mk'_nonempty`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.direction_mk'`：direction_mk' (p : P) (direction : Submodu
le k V) : (mk' p direction).direction = direction
· 使用定理 `Submodule.isCompl_orthogonal`：isCompl_orthogonal [K.HasOrthogonalProject
ion] : IsCompl K Kᗮ where disjoint
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.eq_singleton_iff_nonempty_unique_mem`：eq_singleton_iff_nonempty_uniq
ue_mem : s = {a} ↔ s.Nonempty ∧ forall x in s, x = a
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem_orthogonal`：orthogonalProject
ion_mem_orthogonal (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogo
nalProjection] (p : P) : ↑(orthogonalProjec…

--- 原说明 ---
The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonalProjection` of that point
onto the subspace.
-/
theorem inter_eq_singleton_orthogonalProjection {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    (s : Set P) ∩ mk' p s.directionᗮ = {↑(orthogonalProjection s p)} := by
  obtain ⟨q, hq⟩ := inter_eq_singleton_of_nonempty_of_isCompl (nonempty_subtype.mp ‹_›)
    (mk'_nonempty p s.directionᗮ)
    (by
      rw [direction_mk' p s.directionᗮ]
      exact s.direction.isCompl_orthogonal)
  rwa [Set.eq_singleton_iff_nonempty_unique_mem.1 hq |>.2 _
    ⟨orthogonalProjection_mem _, orthogonalProjection_mem_orthogonal _ _⟩]

/-- Subtracting a point in the given subspace from the
`orthogonalProjection` produces a result in the direction of the
given subspace. -/
/-
**EuclideanGeometry.orthogonalProjection_vsub_mem_direction** 是 Mathlib 中的一个定理，位
于命名空间 `EuclideanGeometry`。
形式化陈述：orthogonalProjection_vsub_mem_direction {s : AffineSubspace 𝕜 P} [Nonempty
 s] [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (hp₁ : p₁ in s) : ↑(
orthogonalProjection s p₂ -ᵥ ⟨p₁, hp₁⟩ : s.direction) in s.direction
参数：p₂ : P；hp₁ : p₁ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
Subtracting a point in the given subspace from the
`orthogonalProjection` produces a result in the direction of the
given subspace.
-/
theorem orthogonalProjection_vsub_mem_direction {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (hp₁ : p₁ ∈ s) :
    ↑(orthogonalProjection s p₂ -ᵥ ⟨p₁, hp₁⟩ : s.direction) ∈ s.direction :=
  (orthogonalProjection s p₂ -ᵥ ⟨p₁, hp₁⟩ : s.direction).2

/-- Subtracting the `orthogonalProjection` from a point in the given
subspace produces a result in the direction of the given subspace. -/
/-
**EuclideanGeometry.vsub_orthogonalProjection_mem_direction** 是 Mathlib 中的一个定理，位
于命名空间 `EuclideanGeometry`。
形式化陈述：vsub_orthogonalProjection_mem_direction {s : AffineSubspace 𝕜 P} [Nonempty
 s] [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (hp₁ : p₁ in s) : ↑(
(⟨p₁, hp₁⟩ : s) -ᵥ orthogonalProjection s p₂ : s.direction) in s.direction
参数：p₂ : P；hp₁ : p₁ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
Subtracting the `orthogonalProjection` from a point in the given
subspace produces a result in the direction of the given subspace.
-/
theorem vsub_orthogonalProjection_mem_direction {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (hp₁ : p₁ ∈ s) :
    ↑((⟨p₁, hp₁⟩ : s) -ᵥ orthogonalProjection s p₂ : s.direction) ∈ s.direction :=
  ((⟨p₁, hp₁⟩ : s) -ᵥ orthogonalProjection s p₂ : s.direction).2

/-- A point equals its orthogonal projection if and only if it lies in
the subspace. -/
/-
**EuclideanGeometry.orthogonalProjection_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：orthogonalProjection_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s] [s.
direction.HasOrthogonalProjection] {p : P} : ↑(orthogonalProjection s p) = p ↔ p
 in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
· 使用定理 `AffineSubspace.self_mem_mk'`：self_mem_mk' (p : P) (direction : Submodule
 k V) : p in mk' p direction
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.inter_eq_singleton_orthogonalProjection`：inter_eq_sing
leton_orthogonalProjection {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.Ha
sOrthogonalProjection] (p : P) : (s : Set P) in…

--- 原说明 ---
A point equals its orthogonal projection if and only if it lies in
the subspace.
-/
theorem orthogonalProjection_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} : ↑(orthogonalProjection s p) = p ↔ p ∈ s := by
  constructor
  · exact fun h => h ▸ orthogonalProjection_mem p
  · intro h
    have hp : p ∈ (s : Set P) ∩ mk' p s.directionᗮ := ⟨h, self_mem_mk' p _⟩
    rw [inter_eq_singleton_orthogonalProjection p] at hp
    symm
    exact hp

@[simp]
/-
**EuclideanGeometry.orthogonalProjection_mem_subspace_eq_self** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：orthogonalProjection_mem_subspace_eq_self {s : AffineSubspace 𝕜 P} [Nonemp
ty s] [s.direction.HasOrthogonalProjection] (p : s) : orthogonalProjection s p =
 p
参数：p : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.orthogonalProjection_eq_self_iff`：orthogonalProjection
_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalPro
jection] {p : P} : ↑(orthogonalProjectio…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem orthogonalProjection_mem_subspace_eq_self {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : s) : orthogonalProjection s p = p := by
  ext
  rw [orthogonalProjection_eq_self_iff]
  exact p.2

/-- Orthogonal projection is idempotent. -/
/-
**EuclideanGeometry.orthogonalProjection_orthogonalProjection** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：orthogonalProjection_orthogonalProjection (s : AffineSubspace 𝕜 P) [Nonemp
ty s] [s.direction.HasOrthogonalProjection] (p : P) : orthogonalProjection s (or
thogonalProjection s p) = orthogonalProjection s p
参数：s : AffineSubspace 𝕜 P；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem_subspace_eq_self`：orthogonalP
rojection_mem_subspace_eq_self {s : AffineSubspace 𝕜 P} [Nonempty s] [s.directio
n.HasOrthogonalProjection] (p : s) : orthogonalPr…

--- 原说明 ---
Orthogonal projection is idempotent.
-/
theorem orthogonalProjection_orthogonalProjection (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    orthogonalProjection s (orthogonalProjection s p) = orthogonalProjection s p :=
  orthogonalProjection_mem_subspace_eq_self ((orthogonalProjection s) p)
/-
**EuclideanGeometry.eq_orthogonalProjection_of_eq_subspace** 是 Mathlib 中的一个定理，位于
命名空间 `EuclideanGeometry`。
形式化陈述：eq_orthogonalProjection_of_eq_subspace {s s' : AffineSubspace 𝕜 P} [Nonemp
ty s] [Nonempty s'] [s.direction.HasOrthogonalProjection] [s'.direction.HasOrtho
gonalProjection] (h : s = s') (p : P) : (orthogonalProjection s p : P) = (orthog
onalProjection s' p : P)
参数：h : s = s'；p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_orthogonalProjection_of_eq_subspace {s s' : AffineSubspace 𝕜 P} [Nonempty s]
    [Nonempty s'] [s.direction.HasOrthogonalProjection] [s'.direction.HasOrthogonalProjection]
    (h : s = s') (p : P) : (orthogonalProjection s p : P) = (orthogonalProjection s' p : P) := by
  subst h
  rfl
/-
**EuclideanGeometry.orthogonalProjection_affineSpan_singleton** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup V]   [inst_2 : InnerProductSpace 𝕜 V] [inst_3 : MetricSpace 
P] [inst_4 : NormedAddTorsor V P] (p₁ p₂ : P),   ↑((EuclideanGeometry.orthogonal
Projection (affineSpan 𝕜 {p₁})) p₂) = p₁
参数：p₁ p₂ : P；(EuclideanGeometry.orthogonalProjection (affineSpan 𝕜 {p₁})) p₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.mem_affineSpan_singleton`：mem_affineSpan_singleton : p₁ i
n affineSpan k ({p₂} : Set P) ↔ p₁ = p₂
-/
@[simp] lemma orthogonalProjection_affineSpan_singleton (p₁ p₂ : P) :
    orthogonalProjection (affineSpan 𝕜 {p₁}) p₂ = p₁ := by
  have h := SetLike.coe_mem (orthogonalProjection (affineSpan 𝕜 {p₁}) p₂)
  rwa [mem_affineSpan_singleton] at h

/-- The distance to a point's orthogonal projection is 0 iff it lies in the subspace. -/
/-
**EuclideanGeometry.dist_orthogonalProjection_eq_zero_iff** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：dist_orthogonalProjection_eq_zero_iff {s : AffineSubspace 𝕜 P} [Nonempty s
] [s.direction.HasOrthogonalProjection] {p : P} : dist p (orthogonalProjection s
 p) = 0 ↔ p in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_eq_zero`：dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y
· 使用定理 `EuclideanGeometry.orthogonalProjection_eq_self_iff`：orthogonalProjection
_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalPro
jection] {p : P} : ↑(orthogonalProjectio…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The distance to a point's orthogonal projection is 0 iff it lies in the subspace
.
-/
theorem dist_orthogonalProjection_eq_zero_iff {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} :
    dist p (orthogonalProjection s p) = 0 ↔ p ∈ s := by
  rw [dist_comm, dist_eq_zero, orthogonalProjection_eq_self_iff]

/-- The distance between a point and its orthogonal projection is
nonzero if it does not lie in the subspace. -/
/-
**EuclideanGeometry.dist_orthogonalProjection_ne_zero_of_notMem** 是 Mathlib 中的一个
定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_orthogonalProjection_ne_zero_of_notMem {s : AffineSubspace 𝕜 P} [None
mpty s] [s.direction.HasOrthogonalProjection] {p : P} (hp : p ∉ s) : dist p (ort
hogonalProjection s p) != 0
参数：hp : p ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.dist_orthogonalProjection_eq_zero_iff`：dist_orthogonal
Projection_eq_zero_iff {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrt
hogonalProjection] {p : P} : dist p (orthogon…

--- 原说明 ---
The distance between a point and its orthogonal projection is
nonzero if it does not lie in the subspace.
-/
theorem dist_orthogonalProjection_ne_zero_of_notMem {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} (hp : p ∉ s) :
    dist p (orthogonalProjection s p) ≠ 0 :=
  mt dist_orthogonalProjection_eq_zero_iff.mp hp

/-- Subtracting `p` from its `orthogonalProjection` produces a result
in the orthogonal direction. -/
/-
**EuclideanGeometry.orthogonalProjection_vsub_mem_direction_orthogonal** 是 Mathl
ib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：orthogonalProjection_vsub_mem_direction_orthogonal (s : AffineSubspace 𝕜 P
) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : (orthogonalProjec
tion s p : P) -ᵥ p in s.directionᗮ
参数：s : AffineSubspace 𝕜 P；p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.mem_mk'`：mem_mk' {p q : P} {direction : Submodule k V} : 
q in mk' p direction ↔ q -ᵥ p in direction
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem_orthogonal`：orthogonalProject
ion_mem_orthogonal (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogo
nalProjection] (p : P) : ↑(orthogonalProjec…

--- 原说明 ---
Subtracting `p` from its `orthogonalProjection` produces a result
in the orthogonal direction.
-/
theorem orthogonalProjection_vsub_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    (orthogonalProjection s p : P) -ᵥ p ∈ s.directionᗮ := by
  rw [← mem_mk']
  apply orthogonalProjection_mem_orthogonal

/-- Subtracting the `orthogonalProjection` from `p` produces a result
in the orthogonal direction. -/
/-
**EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal** 是 Mathl
ib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：vsub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P
) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : p -ᵥ orthogonalPr
ojection s p in s.directionᗮ
参数：s : AffineSubspace 𝕜 P；p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `AffineSubspace.self_mem_mk'`：self_mem_mk' (p : P) (direction : Submodule
 k V) : p in mk' p direction
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem_orthogonal`：orthogonalProject
ion_mem_orthogonal (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogo
nalProjection] (p : P) : ↑(orthogonalProjec…
· 使用定理 `AffineSubspace.direction_mk'`：direction_mk' (p : P) (direction : Submodu
le k V) : (mk' p direction).direction = direction

--- 原说明 ---
Subtracting the `orthogonalProjection` from `p` produces a result
in the orthogonal direction.
-/
theorem vsub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : p -ᵥ orthogonalProjection s p ∈ s.directionᗮ :=
  direction_mk' p s.directionᗮ ▸
    vsub_mem_direction (self_mem_mk' _ _) (orthogonalProjection_mem_orthogonal s p)

/-- Subtracting the `orthogonalProjection` from `p` produces a result in the kernel of the linear
part of the orthogonal projection. -/
/-
**EuclideanGeometry.orthogonalProjection_vsub_orthogonalProjection** 是 Mathlib 中
的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：orthogonalProjection_vsub_orthogonalProjection (s : AffineSubspace 𝕜 P) [N
onempty s] [s.direction.HasOrthogonalProjection] (p : P) : s.direction.orthogona
lProjectionOnto (p -ᵥ orthogonalProjection s p) = 0
参数：s : AffineSubspace 𝕜 P；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal`：vs
ub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : p -…

--- 原说明 ---
Subtracting the `orthogonalProjection` from `p` produces a result in the kernel 
of the linear
part of the orthogonal projection.
-/
theorem orthogonalProjection_vsub_orthogonalProjection (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    s.direction.orthogonalProjectionOnto (p -ᵥ orthogonalProjection s p) = 0 := by
  simpa using vsub_orthogonalProjection_mem_direction_orthogonal _ _

/-- The characteristic property of the orthogonal projection, for a point given in the underlying
space. This form is typically more convenient to use than
`inter_eq_singleton_orthogonalProjection`. -/
/-
**EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem** 是 Mathlib 中的一个引理，位于命名空
间 `EuclideanGeometry`。
形式化陈述：coe_orthogonalProjection_eq_iff_mem {s : AffineSubspace 𝕜 P} [Nonempty s] 
[s.direction.HasOrthogonalProjection] {p q : P} : orthogonalProjection s p = q ↔
 q in s ∧ p -ᵥ q in s.directionᗮ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
· 使用定理 `EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal`：vs
ub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : p -…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.mem_mk'`：mem_mk' {p q : P} {direction : Submodule k V} : 
q in mk' p direction ↔ q -ᵥ p in direction
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `EuclideanGeometry.inter_eq_singleton_orthogonalProjection`：inter_eq_sing
leton_orthogonalProjection {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.Ha
sOrthogonalProjection] (p : P) : (s : Set P) in…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
The characteristic property of the orthogonal projection, for a point given in t
he underlying
space. This form is typically more convenient to use than
`inter_eq_singleton_orthogonalProjection`.
-/
lemma coe_orthogonalProjection_eq_iff_mem {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p q : P} :
    orthogonalProjection s p = q ↔ q ∈ s ∧ p -ᵥ q ∈ s.directionᗮ := by
  constructor
  · rintro rfl
    exact ⟨orthogonalProjection_mem _, vsub_orthogonalProjection_mem_direction_orthogonal _ _⟩
  · rintro ⟨hqs, hpq⟩
    have hq : q ∈ mk' p s.directionᗮ := by
      rwa [mem_mk', ← neg_mem_iff, neg_vsub_eq_vsub_rev]
    suffices q ∈ ({(orthogonalProjection s p : P)} : Set P) by
      simpa [eq_comm] using this
    rw [← inter_eq_singleton_orthogonalProjection]
    simp only [Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨hqs, hq⟩

/-- The characteristic property of the orthogonal projection, for a point given in the relevant
subspace. This form is typically more convenient to use than
`inter_eq_singleton_orthogonalProjection`. -/
/-
**EuclideanGeometry.orthogonalProjection_eq_iff_mem** 是 Mathlib 中的一个引理，位于命名空间 `E
uclideanGeometry`。
形式化陈述：orthogonalProjection_eq_iff_mem {s : AffineSubspace 𝕜 P} [Nonempty s] [s.d
irection.HasOrthogonalProjection] {p : P} {q : s} : orthogonalProjection s p = q
 ↔ p -ᵥ q in s.directionᗮ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem`：coe_orthogonalPro
jection_eq_iff_mem {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogo
nalProjection] {p q : P} : orthogonalProjec…

--- 原说明 ---
The characteristic property of the orthogonal projection, for a point given in t
he relevant
subspace. This form is typically more convenient to use than
`inter_eq_singleton_orthogonalProjection`.
-/
lemma orthogonalProjection_eq_iff_mem {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} {q : s} :
    orthogonalProjection s p = q ↔ p -ᵥ q ∈ s.directionᗮ := by
  simpa using coe_orthogonalProjection_eq_iff_mem (s := s) (p := p) (q := (q : P))

/-- A condition for two points to have the same orthogonal projection onto a given subspace. -/
/-
**EuclideanGeometry.orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem** 
是 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem {s : AffineSubsp
ace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] {p q : P} : orthogon
alProjection s p = orthogonalProjection s q ↔ p -ᵥ q in s.directionᗮ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.orthogonalProjection_eq_iff_mem`：orthogonalProjection_
eq_iff_mem {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProje
ction] {p : P} {q : s} : orthogonalProj…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.add_mem_iff_left`：∀ {R : Type u} {M : Type v} [inst : Ring R] 
[inst_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {
x y : M}, y ∈ p …
· 使用定理 `EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal`：vs
ub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : p -…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A condition for two points to have the same orthogonal projection onto a given s
ubspace.
-/
lemma orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem {s : AffineSubspace 𝕜 P}
    [Nonempty s] [s.direction.HasOrthogonalProjection] {p q : P} :
    orthogonalProjection s p = orthogonalProjection s q ↔ p -ᵥ q ∈ s.directionᗮ := by
  rw [orthogonalProjection_eq_iff_mem, ← s.directionᗮ.add_mem_iff_left (x := p -ᵥ q)
    (vsub_orthogonalProjection_mem_direction_orthogonal s q)]
  simp

/-- If the orthogonal projections of a point onto two subspaces are equal, so is the projection
onto their supremum. -/
/-
**EuclideanGeometry.orthogonalProjection_sup_of_orthogonalProjection_eq** 是 Math
lib 中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：orthogonalProjection_sup_of_orthogonalProjection_eq {s₁ s₂ : AffineSubspac
e 𝕜 P} [Nonempty s₁] [Nonempty s₂] [s₁.direction.HasOrthogonalProjection] [s₂.di
rection.HasOrthogonalProjection] {p : P} (h : (orthogonalProjection s₁ p : P) = 
orthogonalProjection s₂ p) [(s₁ ⊔ s₂).direction.HasOrthogonalProjection] : (orth
ogonalProjection (s₁ ⊔ s₂) p : P) = orthogonalProjection s₁ p
参数：h : (orthogonalProjection s₁ p : P) = orthogonalProjection s₂ p；s₁ ⊔ s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem`：coe_orthogonalPro
jection_eq_iff_mem {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogo
nalProjection] {p q : P} : orthogonalProjec…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
· 使用引理 `AffineSubspace.direction_sup_eq_sup_direction`：direction_sup_eq_sup_dire
ction {s₁ s₂ : AffineSubspace k P} {p : P} (hp₁ : p in s₁) (hp₂ : p in s₂) : (s₁
 ⊔ s₂).direction = s₁.direction ⊔ s…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.inf_orthogonal`：inf_orthogonal (K₁ K₂ : Submodule 𝕜 E) : K₁ᗮ ⊓
 K₂ᗮ = (K₁ ⊔ K₂)ᗮ
· 使用定理 `EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal`：vs
ub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : p -…

--- 原说明 ---
If the orthogonal projections of a point onto two subspaces are equal, so is the
 projection
onto their supremum.
-/
lemma orthogonalProjection_sup_of_orthogonalProjection_eq {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁]
    [Nonempty s₂] [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    {p : P} (h : (orthogonalProjection s₁ p : P) = orthogonalProjection s₂ p)
    [(s₁ ⊔ s₂).direction.HasOrthogonalProjection] :
    (orthogonalProjection (s₁ ⊔ s₂) p : P) = orthogonalProjection s₁ p := by
  rw [coe_orthogonalProjection_eq_iff_mem]
  refine ⟨SetLike.le_def.1 le_sup_left (orthogonalProjection_mem _), ?_⟩
  rw [direction_sup_eq_sup_direction (orthogonalProjection_mem p) (h ▸ orthogonalProjection_mem p),
    ← Submodule.inf_orthogonal]
  exact ⟨vsub_orthogonalProjection_mem_direction_orthogonal _ _,
    h ▸ vsub_orthogonalProjection_mem_direction_orthogonal _ _⟩

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector was
in the orthogonal direction. -/
/-
**EuclideanGeometry.orthogonalProjection_vadd_eq_self** 是 Mathlib 中的一个定理，位于命名空间 
`EuclideanGeometry`。
形式化陈述：orthogonalProjection_vadd_eq_self {s : AffineSubspace 𝕜 P} [Nonempty s] [s
.direction.HasOrthogonalProjection] {p : P} (hp : p in s) {v : V} (hv : v in s.d
irectionᗮ) : orthogonalProjection s (v +ᵥ p) = ⟨p, hp⟩
参数：hp : p in s；hv : v in s.directionᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem`：coe_orthogonalPro
jection_eq_iff_mem {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogo
nalProjection] {p q : P} : orthogonalProjec…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector was
in the orthogonal direction.
-/
theorem orthogonalProjection_vadd_eq_self {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} (hp : p ∈ s) {v : V} (hv : v ∈ s.directionᗮ) :
    orthogonalProjection s (v +ᵥ p) = ⟨p, hp⟩ := by
  ext
  exact coe_orthogonalProjection_eq_iff_mem.mpr (by simp [*])

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point. -/
/-
**EuclideanGeometry.orthogonalProjection_vadd_smul_vsub_orthogonalProjection** 是
 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：orthogonalProjection_vadd_smul_vsub_orthogonalProjection {s : AffineSubspa
ce 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (r 
: 𝕜) (hp : p₁ in s) : orthogonalProjection s (r • (p₂ -ᵥ orthogonalProjection s 
p₂ : V) +ᵥ p₁) = ⟨p₁, hp⟩
参数：p₂ : P；r : 𝕜；hp : p₁ in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.orthogonalProjection_vadd_eq_self`：orthogonalProjectio
n_vadd_eq_self {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalP
rojection] {p : P} (hp : p in s) {v : V} …
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal`：vs
ub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : p -…

--- 原说明 ---
Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point.
-/
theorem orthogonalProjection_vadd_smul_vsub_orthogonalProjection {s : AffineSubspace 𝕜 P}
    [Nonempty s] [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (r : 𝕜) (hp : p₁ ∈ s) :
    orthogonalProjection s (r • (p₂ -ᵥ orthogonalProjection s p₂ : V) +ᵥ p₁) = ⟨p₁, hp⟩ :=
  orthogonalProjection_vadd_eq_self hp
    (Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal s _))
/-
**EuclideanGeometry.orthogonalProjection_orthogonalProjection_of_le** 是 Mathlib 
中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：orthogonalProjection_orthogonalProjection_of_le {s₁ s₂ : AffineSubspace 𝕜 
P} [Nonempty s₁] [Nonempty s₂] [s₁.direction.HasOrthogonalProjection] [s₂.direct
ion.HasOrthogonalProjection] (h : s₁ <= s₂) (p : P) : orthogonalProjection s₁ (o
rthogonalProjection s₂ p) = orthogonalProjection s₁ p
参数：h : s₁ <= s₂；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.orthogonalProjection_eq_orthogonalProjection_iff_vsub_
mem`：orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem {s : AffineSubspa
ce 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] {p q :…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.orthogonal_le`：orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <
= K₂) : K₂ᗮ <= K₁ᗮ
· 使用定理 `AffineSubspace.direction_le`：direction_le {s₁ s₂ : AffineSubspace k P} (
h : s₁ <= s₂) : s₁.direction <= s₂.direction
· 使用定理 `EuclideanGeometry.orthogonalProjection_vsub_mem_direction_orthogonal`：or
thogonalProjection_vsub_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : (or…
-/
lemma orthogonalProjection_orthogonalProjection_of_le {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁]
    [Nonempty s₂] [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (h : s₁ ≤ s₂) (p : P) :
    orthogonalProjection s₁ (orthogonalProjection s₂ p) = orthogonalProjection s₁ p := by
  rw [orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem]
  exact SetLike.le_def.1 (Submodule.orthogonal_le (direction_le h))
    (orthogonalProjection_vsub_mem_direction_orthogonal _ _)

/-- The square of the distance from a point in `s` to `p₂` equals the
sum of the squares of the distances of the two points to the
`orthogonalProjection`. -/
/-
**EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalP
rojection_sq** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq {
s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] {p₁ :
 P} (p₂ : P) (hp₁ : p₁ in s) : dist p₁ p₂ * dist p₁ p₂ = dist p₁ (orthogonalProj
ection s p₂) * dist p₁ (orthogonalProjection s p₂) + dist p₂ (orthogonalProjecti
on s p₂) * dist p₂ (orthogonalProjection s p₂)
参数：p₂ : P；hp₁ : p₁ in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`：norm_add_sq_eq_norm
_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) : ‖x + y‖ * ‖x + y‖ 
= ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖
· 使用定理 `Submodule.inner_right_of_mem_orthogonal`：inner_right_of_mem_orthogonal {
u v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪u, v⟫ = 0
· 使用定理 `EuclideanGeometry.vsub_orthogonalProjection_mem_direction`：vsub_orthogon
alProjection_mem_direction {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.Ha
sOrthogonalProjection] {p₁ : P} (p₂ : P) (hp₁ :…
· 使用定理 `EuclideanGeometry.orthogonalProjection_vsub_mem_direction_orthogonal`：or
thogonalProjection_vsub_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : (or…

--- 原说明 ---
The square of the distance from a point in `s` to `p₂` equals the
sum of the squares of the distances of the two points to the
`orthogonalProjection`.
-/
theorem dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P)
    (hp₁ : p₁ ∈ s) :
    dist p₁ p₂ * dist p₁ p₂ =
      dist p₁ (orthogonalProjection s p₂) * dist p₁ (orthogonalProjection s p₂) +
        dist p₂ (orthogonalProjection s p₂) * dist p₂ (orthogonalProjection s p₂) := by
  rw [dist_comm p₂ _, dist_eq_norm_vsub V p₁ _, dist_eq_norm_vsub V p₁ _, dist_eq_norm_vsub V _ p₂,
    ← vsub_add_vsub_cancel p₁ (orthogonalProjection s p₂) p₂,
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜)]
  exact Submodule.inner_right_of_mem_orthogonal (vsub_orthogonalProjection_mem_direction p₂ hp₁)
    (orthogonalProjection_vsub_mem_direction_orthogonal s p₂)

/-- If the distance from `p₁` to its orthogonal projection equals its distance to a point in `s`,
the orthogonal projection is that point. -/
/-
**EuclideanGeometry.dist_orthogonalProjection_eq_dist_iff_eq_of_mem** 是 Mathlib 
中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_orthogonalProjection_eq_dist_iff_eq_of_mem {s : AffineSubspace 𝕜 P} [
s.direction.HasOrthogonalProjection] {p₁ p₂ : P} (hp₂ : p₂ in s) : haveI : Nonem
pty s
参数：hp₂ : p₂ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `dist_eq_zero`：dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `right_eq_add`：∀ {M : Type u_4} [inst : AddMonoid M] [IsRightCancelAdd M]
 {a b : M}, b = a + b ↔ a = 0
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_ortho
gonalProjection_sq`：dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalP
rojection_sq {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalPro
…
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y

--- 原说明 ---
If the distance from `p₁` to its orthogonal projection equals its distance to a 
point in `s`,
the orthogonal projection is that point.
-/
lemma dist_orthogonalProjection_eq_dist_iff_eq_of_mem {s : AffineSubspace 𝕜 P}
    [s.direction.HasOrthogonalProjection] {p₁ p₂ : P} (hp₂ : p₂ ∈ s) :
    haveI : Nonempty s := ⟨p₂, hp₂⟩
    dist p₁ (orthogonalProjection s p₁) = dist p₁ p₂ ↔ orthogonalProjection s p₁ = p₂ := by
  have : Nonempty s := ⟨p₂, hp₂⟩
  constructor
  · intro h
    rwa [← sq_eq_sq₀ dist_nonneg dist_nonneg, pow_two, pow_two, dist_comm _ p₂,
      dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq _ hp₂,
      right_eq_add, mul_eq_zero, dist_eq_zero, or_self, eq_comm] at h
  · intro h
    nth_rw 4 [← h]

/-- The distance between a point and its orthogonal projection to a subspace equals the distance
to that subspace as given by `Metric.infDist`. This is not a `simp` lemma since the simplest form
depends on the context (if any calculations are to be done with the distance, the version with
the orthogonal projection gives access to more lemmas about orthogonal projections that may be
useful). -/
/-
**EuclideanGeometry.dist_orthogonalProjection_eq_infDist** 是 Mathlib 中的一个引理，位于命名
空间 `EuclideanGeometry`。
形式化陈述：dist_orthogonalProjection_eq_infDist (s : AffineSubspace 𝕜 P) [Nonempty s]
 [s.direction.HasOrthogonalProjection] (p : P) : dist p (orthogonalProjection s 
p) = Metric.infDist p s
参数：s : AffineSubspace 𝕜 P；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infDist_eq_iInf`：infDist_eq_iInf : infDist x s = ⨅ y : s, dist x 
y
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `le_of_sq_le_sq`：le_of_sq_le_sq (h : a ^ 2 <= b ^ 2) (hb : 0 <= b) : a <=
 b
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_ortho
gonalProjection_sq`：dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalP
rojection_sq {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalPro
…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Metric.infDist_le_dist_of_mem`：infDist_le_dist_of_mem (h : y in s) : inf
Dist x s <= dist x y
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…

--- 原说明 ---
The distance between a point and its orthogonal projection to a subspace equals 
the distance
to that subspace as given by `Metric.infDist`. This is not a `simp` lemma since 
the simplest form
depends on the context (if any calculations are to be done with the distance, th
e version with
the orthogonal projection gives access to more lemmas about orthogonal projectio
ns that may be
useful).
-/
lemma dist_orthogonalProjection_eq_infDist (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    dist p (orthogonalProjection s p) = Metric.infDist p s := by
  refine le_antisymm ?_ (Metric.infDist_le_dist_of_mem (orthogonalProjection_mem _))
  rw [Metric.infDist_eq_iInf]
  refine le_ciInf fun x ↦ le_of_sq_le_sq ?_ dist_nonneg
  rw [dist_comm _ (x : P)]
  simp_rw [pow_two,
    dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p x.property]
  simp [mul_self_nonneg]

/-- The nonnegative distance between a point and its orthogonal projection to a subspace equals
the distance to that subspace as given by `Metric.infNndist`. This is not a `simp` lemma since
the simplest form depends on the context (if any calculations are to be done with the distance,
the version with the orthogonal projection gives access to more lemmas about orthogonal
projections that may be useful). -/
/-
**EuclideanGeometry.dist_orthogonalProjection_eq_infNndist** 是 Mathlib 中的一个引理，位于
命名空间 `EuclideanGeometry`。
形式化陈述：dist_orthogonalProjection_eq_infNndist (s : AffineSubspace 𝕜 P) [Nonempty 
s] [s.direction.HasOrthogonalProjection] (p : P) : nndist p (orthogonalProjectio
n s p) = Metric.infNndist p s
参数：s : AffineSubspace 𝕜 P；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `EuclideanGeometry.dist_orthogonalProjection_eq_infDist`：dist_orthogonalP
rojection_eq_infDist (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrtho
gonalProjection] (p : P) : dist p (orthogona…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The nonnegative distance between a point and its orthogonal projection to a subs
pace equals
the distance to that subspace as given by `Metric.infNndist`. This is not a `sim
p` lemma since
the simplest form depends on the context (if any calculations are to be done wit
h the distance,
the version with the orthogonal projection gives access to more lemmas about ort
hogonal
projections that may be useful).
-/
lemma dist_orthogonalProjection_eq_infNndist (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    nndist p (orthogonalProjection s p) = Metric.infNndist p s := by
  rw [← NNReal.coe_inj]
  simp [dist_orthogonalProjection_eq_infDist]

/-- The square of the distance between two points constructed by
adding multiples of the same orthogonal vector to points in the same
subspace. -/
/-
**EuclideanGeometry.dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd** 是 Mathli
b 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd {s : AffineSubspace 𝕜 P}
 {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (r₁ r₂ : 𝕜) {v : V} (hv : v in s.di
rectionᗮ) : dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) * dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ 
p₂) = dist p₁ p₂ * dist p₁ p₂ + ‖r₁ - r₂‖ * ‖r₁ - r₂‖ * (‖v‖ * ‖v‖)
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；r₁ r₂ : 𝕜；hv : v in s.directionᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`：norm_add_sq_eq_norm
_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) : ‖x + y‖ * ‖x + y‖ 
= ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖
· 使用定理 `Submodule.inner_right_of_mem_orthogonal`：inner_right_of_mem_orthogonal {
u v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪u, v⟫ = 0
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The square of the distance between two points constructed by
adding multiples of the same orthogonal vector to points in the same
subspace.
-/
theorem dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd {s : AffineSubspace 𝕜 P} {p₁ p₂ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (r₁ r₂ : 𝕜) {v : V} (hv : v ∈ s.directionᗮ) :
    dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) * dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) =
      dist p₁ p₂ * dist p₁ p₂ + ‖r₁ - r₂‖ * ‖r₁ - r₂‖ * (‖v‖ * ‖v‖) :=
  calc
    dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) * dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) =
        ‖p₁ -ᵥ p₂ + (r₁ - r₂) • v‖ * ‖p₁ -ᵥ p₂ + (r₁ - r₂) • v‖ := by
      rw [dist_eq_norm_vsub V (r₁ • v +ᵥ p₁), vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, sub_smul,
        add_comm, add_sub_assoc]
    _ = ‖p₁ -ᵥ p₂‖ * ‖p₁ -ᵥ p₂‖ + ‖(r₁ - r₂) • v‖ * ‖(r₁ - r₂) • v‖ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
        (Submodule.inner_right_of_mem_orthogonal (vsub_mem_direction hp₁ hp₂)
          (Submodule.smul_mem _ _ hv))
    _ = dist p₁ p₂ * dist p₁ p₂ + ‖r₁ - r₂‖ * ‖r₁ - r₂‖ * (‖v‖ * ‖v‖) := by
      rw [norm_smul, dist_eq_norm_vsub V p₁]
      ring

/-- `p` is equidistant from two points in `s` if and only if its
`orthogonalProjection` is. -/
/-
**EuclideanGeometry.dist_eq_iff_dist_orthogonalProjection_eq** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_eq_iff_dist_orthogonalProjection_eq {s : AffineSubspace 𝕜 P} [Nonempt
y s] [s.direction.HasOrthogonalProjection] {p₁ p₂ : P} (p₃ : P) (hp₁ : p₁ in s) 
(hp₂ : p₂ in s) : dist p₁ p₃ = dist p₂ p₃ ↔ dist p₁ (orthogonalProjection s p₃) 
= dist p₂ (orthogonalProjection s p₃)
参数：p₃ : P；hp₁ : p₁ in s；hp₂ : p₂ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_self_inj_of_nonneg`：mul_self_inj_of_nonneg {α : Type*} [CommRing α] 
[NoZeroDivisors α] [PartialOrder α] [IsStrictOrderedRing α] {a b : α} (a0 : 0 <=
 a) (b0 : 0 …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_ortho
gonalProjection_sq`：dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalP
rojection_sq {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalPro
…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`p` is equidistant from two points in `s` if and only if its
`orthogonalProjection` is.
-/
theorem dist_eq_iff_dist_orthogonalProjection_eq {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ p₂ : P} (p₃ : P) (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) :
    dist p₁ p₃ = dist p₂ p₃ ↔
      dist p₁ (orthogonalProjection s p₃) = dist p₂ (orthogonalProjection s p₃) := by
  rw [← mul_self_inj_of_nonneg dist_nonneg dist_nonneg, ←
    mul_self_inj_of_nonneg dist_nonneg dist_nonneg,
    dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₃ hp₁,
    dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₃ hp₂]
  simp

/-- `p` is equidistant from a set of points in `s` if and only if its
`orthogonalProjection` is. -/
/-
**EuclideanGeometry.dist_set_eq_iff_dist_orthogonalProjection_eq** 是 Mathlib 中的一
个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_set_eq_iff_dist_orthogonalProjection_eq {s : AffineSubspace 𝕜 P} [Non
empty s] [s.direction.HasOrthogonalProjection] {ps : Set P} (hps : ps subseteq s
) (p : P) : (Set.Pairwise ps fun p₁ p₂ => dist p₁ p = dist p₂ p) ↔ Set.Pairwise 
ps fun p₁ p₂ => dist p₁ (orthogonalProjection s p) = dist p₂ (orthogonalProjecti
on s p)
参数：hps : ps subseteq s；p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanGeometry.dist_eq_iff_dist_orthogonalProjection_eq`：dist_eq_iff_
dist_orthogonalProjection_eq {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.
HasOrthogonalProjection] {p₁ p₂ : P} (p₃ : P) (h…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
`p` is equidistant from a set of points in `s` if and only if its
`orthogonalProjection` is.
-/
theorem dist_set_eq_iff_dist_orthogonalProjection_eq {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {ps : Set P} (hps : ps ⊆ s) (p : P) :
    (Set.Pairwise ps fun p₁ p₂ => dist p₁ p = dist p₂ p) ↔
      Set.Pairwise ps fun p₁ p₂ =>
        dist p₁ (orthogonalProjection s p) = dist p₂ (orthogonalProjection s p) :=
  ⟨fun h _ hp₁ _ hp₂ hne =>
    (dist_eq_iff_dist_orthogonalProjection_eq p (hps hp₁) (hps hp₂)).1 (h hp₁ hp₂ hne),
    fun h _ hp₁ _ hp₂ hne =>
    (dist_eq_iff_dist_orthogonalProjection_eq p (hps hp₁) (hps hp₂)).2 (h hp₁ hp₂ hne)⟩

/-- There exists `r` such that `p` has distance `r` from all the
points of a set of points in `s` if and only if there exists (possibly
different) `r` such that its `orthogonalProjection` has that distance
from all the points in that set. -/
/-
**EuclideanGeometry.exists_dist_eq_iff_exists_dist_orthogonalProjection_eq** 是 M
athlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：exists_dist_eq_iff_exists_dist_orthogonalProjection_eq {s : AffineSubspace
 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] {ps : Set P} (hps : ps 
subseteq s) (p : P) : (exists r, forall p₁ in ps, dist p₁ p = r) ↔ exists r, for
all p₁ in ps, dist p₁ ↑(orthogonalProjection s p) = r
参数：hps : ps subseteq s；p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.dist_set_eq_iff_dist_orthogonalProjection_eq`：dist_set
_eq_iff_dist_orthogonalProjection_eq {s : AffineSubspace 𝕜 P} [Nonempty s] [s.di
rection.HasOrthogonalProjection] {ps : Set P} (hps :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
There exists `r` such that `p` has distance `r` from all the
points of a set of points in `s` if and only if there exists (possibly
different) `r` such that its `orthogonalProjection` has that distance
from all the points in that set.
-/
theorem exists_dist_eq_iff_exists_dist_orthogonalProjection_eq {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {ps : Set P} (hps : ps ⊆ s) (p : P) :
    (∃ r, ∀ p₁ ∈ ps, dist p₁ p = r) ↔ ∃ r, ∀ p₁ ∈ ps, dist p₁ ↑(orthogonalProjection s p) = r := by
  have h := dist_set_eq_iff_dist_orthogonalProjection_eq hps p
  simp_rw [Set.pairwise_eq_iff_exists_eq] at h
  exact h

/-- Reflection in an affine subspace, which is expected to be nonempty
and complete. The word "reflection" is sometimes understood to mean
specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point. The
definition here, of reflection in an affine subspace, is a more
general sense of the word that includes both those common cases. -/
/-
**EuclideanGeometry.reflection** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGeometry`。
形式化陈述：reflection (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogona
lProjection] : P ≃ᵃⁱ[𝕜] P
参数：s : AffineSubspace 𝕜 P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reflection in an affine subspace, which is expected to be nonempty
and complete. The word "reflection" is sometimes understood to mean
specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point. The
definition here, of reflection in an affine subspace, is a more
general sense of the word that includes both those common cases.
-/
def reflection (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] :
    P ≃ᵃⁱ[𝕜] P :=
  letI x : P := Classical.arbitrary s
  AffineIsometryEquiv.vaddConst 𝕜 x
    |>.symm.trans s.direction.reflection.toAffineIsometryEquiv
    |>.trans <| AffineIsometryEquiv.vaddConst 𝕜 x
/-
**EuclideanGeometry.reflection_apply** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometr
y`。
形式化陈述：reflection_apply (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrt
hogonalProjection] (p : P) : reflection s p = s.direction.reflection (p -ᵥ Class
ical.arbitrary s) +ᵥ (Classical.arbitrary s : P)
参数：s : AffineSubspace 𝕜 P；p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reflection_apply (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection]
    (p : P) :
    reflection s p = s.direction.reflection (p -ᵥ Classical.arbitrary s)
      +ᵥ (Classical.arbitrary s : P) :=
  rfl
/-
**EuclideanGeometry.reflection_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean
Geometry`。
形式化陈述：reflection_apply_of_mem (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction
.HasOrthogonalProjection] (p : P) {x} (hx : x in s) : reflection s p = s.directi
on.reflection (p -ᵥ x) +ᵥ x
参数：s : AffineSubspace 𝕜 P；p : P；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.reflection_apply`：reflection_apply (s : AffineSubspace
 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : reflection s 
p = s.direction.reflecti…
· 使用定理 `vadd_eq_vadd_iff_sub_eq_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : Ad
dCommGroup G] [inst_1 : AddTorsor G P] {v₁ v₂ : G} {p₁ p₂ : P},   v₁ +ᵥ p₁ = v₂ 
+ᵥ p₂ ↔ v₂ - v₁ = …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用定理 `Submodule.reflection_eq_self_iff`：reflection_eq_self_iff (x : E) : K.ref
lection x = x ↔ x in K
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
-/
theorem reflection_apply_of_mem (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) {x} (hx : x ∈ s) :
    reflection s p = s.direction.reflection (p -ᵥ x) +ᵥ x := by
  rw [reflection_apply, vadd_eq_vadd_iff_sub_eq_vsub, ← map_sub,
    vsub_sub_vsub_cancel_left, s.direction.reflection_eq_self_iff]
  exact s.vsub_mem_direction (SetLike.coe_mem _) hx
/-
**EuclideanGeometry.reflection_apply'** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeomet
ry`。
形式化陈述：reflection_apply' (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOr
thogonalProjection] (p : P) : reflection s p = (↑(orthogonalProjection s p) -ᵥ p
) +ᵥ (orthogonalProjection s p : P)
参数：s : AffineSubspace 𝕜 P；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.reflection_apply`：reflection_apply (s : AffineSubspace
 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : reflection s 
p = s.direction.reflecti…
· 使用定理 `EuclideanGeometry.orthogonalProjection_apply'`：orthogonalProjection_appl
y' (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] {
p} : (orthogonalProjection s p : P)…
· 使用引理 `Submodule.coe_orthogonalProjectionOnto_apply`：coe_orthogonalProjectionOn
to_apply (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (v : E) : U.orthogonalP
rojectionOnto v = U.starProjection…
· 使用定理 `Submodule.reflection_apply`：reflection_apply (p : E) : K.reflection p = 
2 • K.starProjection p - p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AddSemigroupAction.add_vadd`：∀ {G : Type u_9} {P : Type u_10} {inst : Ad
dSemigroup G} [self : AddSemigroupAction G P] (g₁ g₂ : G) (p : P),   (g₁ + g₂) +
ᵥ p = g₁ +ᵥ g₂ +ᵥ…
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
-/
theorem reflection_apply' (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    reflection s p = (↑(orthogonalProjection s p) -ᵥ p) +ᵥ (orthogonalProjection s p : P) := by
  rw [reflection_apply, orthogonalProjection_apply', Submodule.coe_orthogonalProjectionOnto_apply]
  set x : P := ↑(Classical.arbitrary s)
  set v : V := s.direction.starProjection (p -ᵥ x)
  rw [Submodule.reflection_apply, two_smul, sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_assoc,
    add_comm v, add_vadd, vadd_vsub_assoc]
/-
**EuclideanGeometry.eq_reflection_of_eq_subspace** 是 Mathlib 中的一个定理，位于命名空间 `Eucl
ideanGeometry`。
形式化陈述：eq_reflection_of_eq_subspace {s s' : AffineSubspace 𝕜 P} [Nonempty s] [Non
empty s'] [s.direction.HasOrthogonalProjection] [s'.direction.HasOrthogonalProje
ction] (h : s = s') (p : P) : (reflection s p : P) = (reflection s' p : P)
参数：h : s = s'；p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_reflection_of_eq_subspace {s s' : AffineSubspace 𝕜 P} [Nonempty s] [Nonempty s']
    [s.direction.HasOrthogonalProjection] [s'.direction.HasOrthogonalProjection] (h : s = s')
    (p : P) : (reflection s p : P) = (reflection s' p : P) := by
  subst h
  rfl

/-- Reflecting twice in the same subspace. -/
@[simp]
/-
**EuclideanGeometry.reflection_reflection** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGe
ometry`。
形式化陈述：reflection_reflection (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.H
asOrthogonalProjection] (p : P) : reflection s (reflection s p) = p
参数：s : AffineSubspace 𝕜 P；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometryEquiv.coe_toAffineIsometryEquiv`：coe_toAffineIsometryEquiv
 : ⇑(e.toAffineIsometryEquiv : V ≃ᵃⁱ[𝕜] V₂) = e
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `Submodule.reflection_reflection`：reflection_reflection (p : E) : K.refle
ction (K.reflection p) = p
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Reflecting twice in the same subspace.
-/
theorem reflection_reflection (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : reflection s (reflection s p) = p := by
  simp [reflection, -AffineIsometryEquiv.map_vadd]

/-- Reflection is its own inverse. -/
@[simp]
/-
**EuclideanGeometry.reflection_symm** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
`。
形式化陈述：reflection_symm (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrth
ogonalProjection] : (reflection s).symm = reflection s
参数：s : AffineSubspace 𝕜 P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometryEquiv.ext`：ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : forall x, e x = e
' x) : e = e'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AffineIsometryEquiv.injective`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Typ
e u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semin
ormedAddCommGroup V…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AffineIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : P₂) : e (e.s
ymm x) = x
· 使用定理 `EuclideanGeometry.reflection_reflection`：reflection_reflection (s : Affi
neSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : ref
lection s (reflection s p) = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Reflection is its own inverse.
-/
theorem reflection_symm (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] : (reflection s).symm = reflection s := by
  ext
  rw [← (reflection s).injective.eq_iff]
  simp

/-- Reflection is involutive. -/
/-
**EuclideanGeometry.reflection_involutive** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGe
ometry`。
形式化陈述：reflection_involutive (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.H
asOrthogonalProjection] : Function.Involutive (reflection s)
参数：s : AffineSubspace 𝕜 P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.reflection_reflection`：reflection_reflection (s : Affi
neSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : ref
lection s (reflection s p) = …

--- 原说明 ---
Reflection is involutive.
-/
theorem reflection_involutive (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] : Function.Involutive (reflection s) :=
  reflection_reflection s

/-- A point is its own reflection if and only if it is in the subspace. -/
/-
**EuclideanGeometry.reflection_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanG
eometry`。
形式化陈述：reflection_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.
HasOrthogonalProjection] (p : P) : reflection s p = p ↔ p in s
参数：p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.reflection_apply`：reflection_apply (s : AffineSubspace
 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : reflection s 
p = s.direction.reflecti…
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_vadd_iff_vsub_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p₁ : P) (g : G) (p₂ : P),   p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g
· 使用定理 `Submodule.reflection_eq_self_iff`：reflection_eq_self_iff (x : E) : K.ref
lection x = x ↔ x in K
· 使用定理 `AffineSubspace.mem_direction_iff_eq_vsub_right`：mem_direction_iff_eq_vsu
b_right {s : AffineSubspace k P} {p : P} (hp : p in s) (v : V) : v in s.directio
n ↔ exists p₂ in s, v = p₂ -ᵥ p
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A point is its own reflection if and only if it is in the subspace.
-/
theorem reflection_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : reflection s p = p ↔ p ∈ s := by
  rw [reflection_apply, Eq.comm, eq_vadd_iff_vsub_eq, Eq.comm, s.direction.reflection_eq_self_iff,
    s.mem_direction_iff_eq_vsub_right (SetLike.coe_mem (Classical.arbitrary s))]
  simp

/-- Reflecting a point in two subspaces produces the same result if
and only if the point has the same orthogonal projection in each of
those subspaces. -/
/-
**EuclideanGeometry.reflection_eq_iff_orthogonalProjection_eq** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：reflection_eq_iff_orthogonalProjection_eq (s₁ s₂ : AffineSubspace 𝕜 P) [No
nempty s₁] [Nonempty s₂] [s₁.direction.HasOrthogonalProjection] [s₂.direction.Ha
sOrthogonalProjection] (p : P) : reflection s₁ p = reflection s₂ p ↔ (orthogonal
Projection s₁ p : P) = orthogonalProjection s₂ p
参数：s₁ s₂ : AffineSubspace 𝕜 P；p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.reflection_apply'`：reflection_apply' (s : AffineSubspa
ce 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : reflection 
s p = (↑(orthogonalProjec…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂

--- 原说明 ---
Reflecting a point in two subspaces produces the same result if
and only if the point has the same orthogonal projection in each of
those subspaces.
-/
theorem reflection_eq_iff_orthogonalProjection_eq (s₁ s₂ : AffineSubspace 𝕜 P) [Nonempty s₁]
    [Nonempty s₂] [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (p : P) :
    reflection s₁ p = reflection s₂ p ↔
      (orthogonalProjection s₁ p : P) = orthogonalProjection s₂ p := by
  rw [reflection_apply', reflection_apply']
  constructor
  · intro h
    rw [← @vsub_eq_zero_iff_eq V, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm, add_sub_assoc,
      vsub_sub_vsub_cancel_right, ←
      two_smul 𝕜 ((orthogonalProjection s₁ p : P) -ᵥ orthogonalProjection s₂ p), smul_eq_zero] at h
    simpa using h
  · intro h
    rw [h]

/-- The distance between `p₁` and the reflection of `p₂` equals that
between the reflection of `p₁` and `p₂`. -/
/-
**EuclideanGeometry.dist_reflection** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry
`。
形式化陈述：dist_reflection (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrth
ogonalProjection] (p₁ p₂ : P) : dist p₁ (reflection s p₂) = dist (reflection s p
₁) p₂
参数：s : AffineSubspace 𝕜 P；p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.reflection_reflection`：reflection_reflection (s : Affi
neSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : ref
lection s (reflection s p) = …
· 使用定理 `AffineIsometryEquiv.dist_map`：dist_map (x y : P) : dist (e x) (e y) = di
st x y

--- 原说明 ---
The distance between `p₁` and the reflection of `p₂` equals that
between the reflection of `p₁` and `p₂`.
-/
theorem dist_reflection (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection]
    (p₁ p₂ : P) : dist p₁ (reflection s p₂) = dist (reflection s p₁) p₂ := by
  conv_lhs => rw [← reflection_reflection s p₁]
  exact (reflection s).dist_map _ _

/-- A point in the subspace is equidistant from another point and its
reflection. -/
/-
**EuclideanGeometry.dist_reflection_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Euclide
anGeometry`。
形式化陈述：dist_reflection_eq_of_mem (s : AffineSubspace 𝕜 P) [Nonempty s] [s.directi
on.HasOrthogonalProjection] {p₁ : P} (hp₁ : p₁ in s) (p₂ : P) : dist p₁ (reflect
ion s p₂) = dist p₁ p₂
参数：s : AffineSubspace 𝕜 P；hp₁ : p₁ in s；p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.reflection_eq_self_iff`：reflection_eq_self_iff {s : Af
fineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : r
eflection s p = p ↔ p in s
· 使用定理 `AffineIsometryEquiv.dist_map`：dist_map (x y : P) : dist (e x) (e y) = di
st x y

--- 原说明 ---
A point in the subspace is equidistant from another point and its
reflection.
-/
theorem dist_reflection_eq_of_mem (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (hp₁ : p₁ ∈ s) (p₂ : P) :
    dist p₁ (reflection s p₂) = dist p₁ p₂ := by
  rw [← reflection_eq_self_iff p₁] at hp₁
  convert! (reflection s).dist_map p₁ p₂
  rw [hp₁]

/-- The reflection of a point in a subspace is contained in any larger
subspace containing both the point and the subspace reflected in. -/
/-
**EuclideanGeometry.reflection_mem_of_le_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Eucli
deanGeometry`。
形式化陈述：reflection_mem_of_le_of_mem {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁] [s₁
.direction.HasOrthogonalProjection] (hle : s₁ <= s₂) {p : P} (hp : p in s₂) : re
flection s₁ p in s₂
参数：hle : s₁ <= s₂；hp : p in s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.reflection_apply'`：reflection_apply' (s : AffineSubspa
ce 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : reflection 
s p = (↑(orthogonalProjec…
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction

--- 原说明 ---
The reflection of a point in a subspace is contained in any larger
subspace containing both the point and the subspace reflected in.
-/
theorem reflection_mem_of_le_of_mem {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁]
    [s₁.direction.HasOrthogonalProjection] (hle : s₁ ≤ s₂) {p : P} (hp : p ∈ s₂) :
    reflection s₁ p ∈ s₂ := by
  rw [reflection_apply']
  have ho : ↑(orthogonalProjection s₁ p) ∈ s₂ := hle (orthogonalProjection_mem p)
  exact vadd_mem_of_mem_direction (vsub_mem_direction ho hp) ho

/-- Reflecting an orthogonal vector plus a point in the subspace
produces the negation of that vector plus the point. -/
/-
**EuclideanGeometry.reflection_orthogonal_vadd** 是 Mathlib 中的一个定理，位于命名空间 `Euclid
eanGeometry`。
形式化陈述：reflection_orthogonal_vadd {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direct
ion.HasOrthogonalProjection] {p : P} (hp : p in s) {v : V} (hv : v in s.directio
nᗮ) : reflection s (v +ᵥ p) = -v +ᵥ p
参数：hp : p in s；hv : v in s.directionᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.reflection_apply'`：reflection_apply' (s : AffineSubspa
ce 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : reflection 
s p = (↑(orthogonalProjec…
· 使用定理 `EuclideanGeometry.orthogonalProjection_vadd_eq_self`：orthogonalProjectio
n_vadd_eq_self {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalP
rojection] {p : P} (hp : p in s) {v : V} …
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Reflecting an orthogonal vector plus a point in the subspace
produces the negation of that vector plus the point.
-/
theorem reflection_orthogonal_vadd {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} (hp : p ∈ s) {v : V} (hv : v ∈ s.directionᗮ) :
    reflection s (v +ᵥ p) = -v +ᵥ p := by
  rw [reflection_apply', orthogonalProjection_vadd_eq_self hp hv, vsub_vadd_eq_vsub_sub]
  simp

/-- Reflecting a vector plus a point in the subspace produces the
negation of that vector plus the point if the vector is a multiple of
the result of subtracting a point's orthogonal projection from that
point. -/
/-
**EuclideanGeometry.reflection_vadd_smul_vsub_orthogonalProjection** 是 Mathlib 中
的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：reflection_vadd_smul_vsub_orthogonalProjection {s : AffineSubspace 𝕜 P} [N
onempty s] [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (r : 𝕜) (hp₁ 
: p₁ in s) : reflection s (r • (p₂ -ᵥ orthogonalProjection s p₂) +ᵥ p₁) = -(r • 
(p₂ -ᵥ orthogonalProjection s p₂)) +ᵥ p₁
参数：p₂ : P；r : 𝕜；hp₁ : p₁ in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.reflection_orthogonal_vadd`：reflection_orthogonal_vadd
 {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] {p 
: P} (hp : p in s) {v : V} (hv : v…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal`：vs
ub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : p -…

--- 原说明 ---
Reflecting a vector plus a point in the subspace produces the
negation of that vector plus the point if the vector is a multiple of
the result of subtracting a point's orthogonal projection from that
point.
-/
theorem reflection_vadd_smul_vsub_orthogonalProjection {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (r : 𝕜) (hp₁ : p₁ ∈ s) :
    reflection s (r • (p₂ -ᵥ orthogonalProjection s p₂) +ᵥ p₁) =
      -(r • (p₂ -ᵥ orthogonalProjection s p₂)) +ᵥ p₁ :=
  reflection_orthogonal_vadd hp₁
    (Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal s _))

variable [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
/-
**EuclideanGeometry.orthogonalProjection_map** 是 Mathlib 中的一个定理，位于命名空间 `Euclidea
nGeometry`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup V]   [inst_2 : InnerProductSpace 𝕜 V] {V₂ : Type u_4} {P₂ : 
Type u_5} [inst_3 : NormedAddCommGroup V₂]   [inst_4 : InnerProductSpace 𝕜 V₂] [
inst_5 : MetricSpace P] [inst_6 : NormedAddTorsor V P] [inst_7 : MetricSpace P₂]
   [inst_8 : NormedAddTorsor V₂ P₂] (s : AffineSubspace 𝕜 P) [inst_9 : Nonempty 
↥s]   [inst_10 : s.direction.HasOrthogonalProjection] (f : P →ᵃⁱ[𝕜] P₂)   [inst_
11 : (AffineSubspace.map f.toAffineMap s).direction.HasOrthogonalProjection] (p 
: P),   ↑((EuclideanGeometry.orthogonalProjection (AffineSubspace.map f.toAffine
Map s)) (f p)) =     f ↑((EuclideanGeometry.orthogonalProjection s) p)
参数：s : AffineSubspace 𝕜 P；f : P →ᵃⁱ[𝕜] P₂；AffineSubspace.map f.toAffineMap s；p :
 P；(EuclideanGeometry.orthogonalProjection (AffineSubspace.map f.toAffineMap s))
 (f p)；(EuclideanGeometry.orthogonalProjection s) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem`：coe_orthogonalPro
jection_eq_iff_mem {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogo
nalProjection] {p q : P} : orthogonalProjec…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AffineIsometry.coe_toAffineMap`：coe_toAffineMap : ⇑f.toAffineMap = f
· 使用定理 `AffineSubspace.map_direction`：map_direction (s : AffineSubspace k P₁) : 
(s.map f).direction = s.direction.map f.linear
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `AffineIsometry.linear_eq_linearIsometry`：linear_eq_linearIsometry : f.li
near = f.linearIsometry.toLinearMap
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
· 使用定理 `Submodule.mem_orthogonal`：mem_orthogonal (v : E) : v in Kᗮ ↔ forall u in
 K, ⟪u, v⟫ = 0
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
· 使用定理 `LinearIsometry.coe_toLinearMap`：coe_toLinearMap : ⇑f.toLinearMap = f
· 使用定理 `LinearIsometry.inner_map_map`：LinearIsometry.inner_map_map (f : E ->ₗᵢ[𝕜
] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `Submodule.inner_right_of_mem_orthogonal`：inner_right_of_mem_orthogonal {
u v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪u, v⟫ = 0
· 使用定理 `EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal`：vs
ub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : p -…
-/
@[simp] lemma orthogonalProjection_map (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (f : P →ᵃⁱ[𝕜] P₂)
    [(s.map f.toAffineMap).direction.HasOrthogonalProjection] (p : P) :
    orthogonalProjection (s.map f.toAffineMap) (f p) = f (orthogonalProjection s p) := by
  rw [coe_orthogonalProjection_eq_iff_mem]
  simp only [mem_map, AffineIsometry.coe_toAffineMap, AffineIsometry.map_eq_iff, exists_eq_right,
    SetLike.coe_mem, map_direction, AffineIsometry.linear_eq_linearIsometry, true_and]
  rw [← AffineIsometry.coe_toAffineMap, ← AffineMap.linearMap_vsub, Submodule.mem_orthogonal]
  intro u hu
  rw [Submodule.mem_map] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  rw [AffineIsometry.linear_eq_linearIsometry, LinearIsometry.coe_toLinearMap,
    LinearIsometry.inner_map_map, Submodule.inner_right_of_mem_orthogonal hv
      (vsub_orthogonalProjection_mem_direction_orthogonal _ _)]
/-
**EuclideanGeometry.orthogonalProjection_subtype** 是 Mathlib 中的一个引理，位于命名空间 `Eucl
ideanGeometry`。
形式化陈述：orthogonalProjection_subtype (s : AffineSubspace 𝕜 P) [Nonempty s] (s' : A
ffineSubspace 𝕜 s) [Nonempty s'] [s'.direction.HasOrthogonalProjection] [(s'.map
 s.subtype).direction.HasOrthogonalProjection] (p : s) : (orthogonalProjection s
' p : P) = orthogonalProjection (s'.map s.subtype) p
参数：s : AffineSubspace 𝕜 P；s' : AffineSubspace 𝕜 s；s'.map s.subtype；p : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `AffineSubspace.subtypeₐᵢ_toAffineMap`：subtypeₐᵢ_toAffineMap (s : AffineS
ubspace 𝕜 P) [Nonempty s] : s.subtypeₐᵢ.toAffineMap = s.subtype
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.orthogonalProjection_congr`：orthogonalProjection_congr
 {s₁ s₂ : AffineSubspace 𝕜 P} {p₁ p₂ : P} [Nonempty s₁] [s₁.direction.HasOrthogo
nalProjection] (h : s₁ = s₂) (hp :…
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `EuclideanGeometry.orthogonalProjection_map`：∀ {𝕜 : Type u_1} {V : Type u
_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2 :
 InnerProductSpace 𝕜 V] {V₂ : Ty…
-/
lemma orthogonalProjection_subtype (s : AffineSubspace 𝕜 P) [Nonempty s] (s' : AffineSubspace 𝕜 s)
    [Nonempty s'] [s'.direction.HasOrthogonalProjection]
    [(s'.map s.subtype).direction.HasOrthogonalProjection] (p : s) :
    (orthogonalProjection s' p : P) = orthogonalProjection (s'.map s.subtype) p := by
  rw [eq_comm]
  have : (s'.map s.subtypeₐᵢ.toAffineMap).direction.HasOrthogonalProjection := by
    rw [subtypeₐᵢ_toAffineMap]
    infer_instance
  convert! orthogonalProjection_map s' s.subtypeₐᵢ p
/-
**EuclideanGeometry.reflection_map** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry`
。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup V]   [inst_2 : InnerProductSpace 𝕜 V] {V₂ : Type u_4} {P₂ : 
Type u_5} [inst_3 : NormedAddCommGroup V₂]   [inst_4 : InnerProductSpace 𝕜 V₂] [
inst_5 : MetricSpace P] [inst_6 : NormedAddTorsor V P] [inst_7 : MetricSpace P₂]
   [inst_8 : NormedAddTorsor V₂ P₂] (s : AffineSubspace 𝕜 P) [inst_9 : Nonempty 
↥s]   [inst_10 : s.direction.HasOrthogonalProjection] (f : P →ᵃⁱ[𝕜] P₂)   [inst_
11 : (AffineSubspace.map f.toAffineMap s).direction.HasOrthogonalProjection] (p 
: P),   (EuclideanGeometry.reflection (AffineSubspace.map f.toAffineMap s)) (f p
) = f ((EuclideanGeometry.reflection s) p)
参数：s : AffineSubspace 𝕜 P；f : P →ᵃⁱ[𝕜] P₂；AffineSubspace.map f.toAffineMap s；p :
 P；EuclideanGeometry.reflection (AffineSubspace.map f.toAffineMap s)；f p；(Euclid
eanGeometry.reflection s) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.reflection_apply'`：reflection_apply' (s : AffineSubspa
ce 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : reflection 
s p = (↑(orthogonalProjec…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EuclideanGeometry.orthogonalProjection_map`：∀ {𝕜 : Type u_1} {V : Type u
_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2 :
 InnerProductSpace 𝕜 V] {V₂ : Ty…
· 使用定理 `AffineIsometry.map_vadd`：map_vadd (p : P) (v : V) : f (v +ᵥ p) = f.linea
rIsometry v +ᵥ f p
· 使用定理 `AffineIsometry.map_vsub`：map_vsub (p1 p2 : P) : f.linearIsometry (p1 -ᵥ 
p2) = f p1 -ᵥ f p2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma reflection_map (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (f : P →ᵃⁱ[𝕜] P₂)
    [(s.map f.toAffineMap).direction.HasOrthogonalProjection] (p : P) :
    reflection (s.map f.toAffineMap) (f p) = f (reflection s p) := by
  simp [reflection_apply']
/-
**EuclideanGeometry.reflection_subtype** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanGeome
try`。
形式化陈述：reflection_subtype (s : AffineSubspace 𝕜 P) [Nonempty s] (s' : AffineSubsp
ace 𝕜 s) [Nonempty s'] [s'.direction.HasOrthogonalProjection] [(s'.map s.subtype
).direction.HasOrthogonalProjection] (p : s) : (reflection s' p : P) = reflectio
n (s'.map s.subtype) p
参数：s : AffineSubspace 𝕜 P；s' : AffineSubspace 𝕜 s；s'.map s.subtype；p : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.reflection_apply'`：reflection_apply' (s : AffineSubspa
ce 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : reflection 
s p = (↑(orthogonalProjec…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `EuclideanGeometry.orthogonalProjection_subtype`：orthogonalProjection_sub
type (s : AffineSubspace 𝕜 P) [Nonempty s] (s' : AffineSubspace 𝕜 s) [Nonempty s
'] [s'.direction.HasOrthogonalProjec…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reflection_subtype (s : AffineSubspace 𝕜 P) [Nonempty s] (s' : AffineSubspace 𝕜 s)
    [Nonempty s'] [s'.direction.HasOrthogonalProjection]
    [(s'.map s.subtype).direction.HasOrthogonalProjection] (p : s) :
    (reflection s' p : P) = reflection (s'.map s.subtype) p := by
  simp [reflection_apply', orthogonalProjection_subtype]

end EuclideanGeometry

namespace Affine

namespace Simplex

open EuclideanGeometry

variable {𝕜 : Type*} {V : Type*} {P : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace 𝕜 V₂]

variable [MetricSpace P] [NormedAddTorsor V P]

/-- The orthogonal projection of a point `p` onto the hyperplane spanned by the simplex's points. -/
/-
**Affine.Simplex.orthogonalProjectionSpan** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simp
lex`。
形式化陈述：orthogonalProjectionSpan {n : Nat} (s : Simplex 𝕜 P n) : P ->ᴬ[𝕜] affineSp
an 𝕜 (Set.range s.points)
参数：s : Simplex 𝕜 P n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthogonal projection of a point `p` onto the hyperplane spanned by the simp
lex's points.
-/
def orthogonalProjectionSpan {n : ℕ} (s : Simplex 𝕜 P n) :
    P →ᴬ[𝕜] affineSpan 𝕜 (Set.range s.points) :=
  orthogonalProjection (affineSpan 𝕜 (Set.range s.points))
/-
**Affine.Simplex.orthogonalProjectionSpan_congr** 是 Mathlib 中的一个引理，位于命名空间 `Affin
e.Simplex`。
形式化陈述：orthogonalProjectionSpan_congr {m n : Nat} {s₁ : Simplex 𝕜 P m} {s₂ : Simp
lex 𝕜 P n} {p₁ p₂ : P} (h : Set.range s₁.points = Set.range s₂.points) (hp : p₁ 
= p₂) : (s₁.orthogonalProjectionSpan p₁ : P) = s₂.orthogonalProjectionSpan p₂
参数：h : Set.range s₁.points = Set.range s₂.points；hp : p₁ = p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.orthogonalProjection_congr`：orthogonalProjection_congr
 {s₁ s₂ : AffineSubspace 𝕜 P} {p₁ p₂ : P} [Nonempty s₁] [s₁.direction.HasOrthogo
nalProjection] (h : s₁ = s₂) (hp :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma orthogonalProjectionSpan_congr {m n : ℕ} {s₁ : Simplex 𝕜 P m} {s₂ : Simplex 𝕜 P n}
    {p₁ p₂ : P} (h : Set.range s₁.points = Set.range s₂.points) (hp : p₁ = p₂) :
    (s₁.orthogonalProjectionSpan p₁ : P) = s₂.orthogonalProjectionSpan p₂ :=
  orthogonalProjection_congr (by rw [h]) hp
/-
**Affine.Simplex.orthogonalProjectionSpan_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ine.Simplex`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup V]   [inst_2 : InnerProductSpace 𝕜 V] [inst_3 : MetricSpace 
P] [inst_4 : NormedAddTorsor V P] {m n : ℕ}   (s : Affine.Simplex 𝕜 P m) (e : Fi
n (m + 1) ≃ Fin (n + 1)) (p : P),   ↑((s.reindex e).orthogonalProjectionSpan p) 
= ↑(s.orthogonalProjectionSpan p)
参数：s : Affine.Simplex 𝕜 P m；e : Fin (m + 1) ≃ Fin (n + 1)；p : P；(s.reindex e).or
thogonalProjectionSpan p；s.orthogonalProjectionSpan p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.orthogonalProjectionSpan_congr`：orthogonalProjectionSpan_
congr {m n : Nat} {s₁ : Simplex 𝕜 P m} {s₂ : Simplex 𝕜 P n} {p₁ p₂ : P} (h : Set
.range s₁.points = Set.range s₂.poi…
· 使用定理 `Affine.Simplex.reindex_range_points`：reindex_range_points {m n : Nat} (s
 : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : Set.range (s.reindex e).poin
ts = Set.range s.points
-/
@[simp] lemma orthogonalProjectionSpan_reindex {m n : ℕ} (s : Simplex 𝕜 P m)
    (e : Fin (m + 1) ≃ Fin (n + 1)) (p : P) :
    ((s.reindex e).orthogonalProjectionSpan p : P) = s.orthogonalProjectionSpan p :=
  orthogonalProjectionSpan_congr (s.reindex_range_points e) rfl

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point. -/
/-
**Affine.Simplex.orthogonalProjection_vadd_smul_vsub_orthogonalProjection** 是 Ma
thlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：orthogonalProjection_vadd_smul_vsub_orthogonalProjection {n : Nat} (s : Si
mplex 𝕜 P n) {p₁ : P} (p₂ : P) (r : 𝕜) (hp : p₁ in affineSpan 𝕜 (Set.range s.poi
nts)) : s.orthogonalProjectionSpan (r • (p₂ -ᵥ s.orthogonalProjectionSpan p₂ : V
) +ᵥ p₁) = ⟨p₁, hp⟩
参数：s : Simplex 𝕜 P n；p₂ : P；r : 𝕜；hp : p₁ in affineSpan 𝕜 (Set.range s.points)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.orthogonalProjection_vadd_smul_vsub_orthogonalProjecti
on`：orthogonalProjection_vadd_smul_vsub_orthogonalProjection {s : AffineSubspace
 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] {p₁ : P…

--- 原说明 ---
Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point.
-/
theorem orthogonalProjection_vadd_smul_vsub_orthogonalProjection {n : ℕ} (s : Simplex 𝕜 P n)
    {p₁ : P} (p₂ : P) (r : 𝕜) (hp : p₁ ∈ affineSpan 𝕜 (Set.range s.points)) :
    s.orthogonalProjectionSpan (r • (p₂ -ᵥ s.orthogonalProjectionSpan p₂ : V) +ᵥ p₁) = ⟨p₁, hp⟩ :=
  EuclideanGeometry.orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ _
/-
**Affine.Simplex.coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection** 
是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection {n : Nat} {r₁
 : 𝕜} (s : Simplex 𝕜 P n) {p p₁o : P} (hp₁o : p₁o in affineSpan 𝕜 (Set.range s.p
oints)) : ↑(s.orthogonalProjectionSpan (r₁ • (p -ᵥ ↑(s.orthogonalProjectionSpan 
p)) +ᵥ p₁o)) = p₁o
参数：s : Simplex 𝕜 P n；hp₁o : p₁o in affineSpan 𝕜 (Set.range s.points)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Affine.Simplex.orthogonalProjection_vadd_smul_vsub_orthogonalProjection`
：orthogonalProjection_vadd_smul_vsub_orthogonalProjection {n : Nat} (s : Simplex
 𝕜 P n) {p₁ : P} (p₂ : P) (r : 𝕜) (hp : p₁ in affineSpan 𝕜 (S…
-/
theorem coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection {n : ℕ} {r₁ : 𝕜}
    (s : Simplex 𝕜 P n) {p p₁o : P} (hp₁o : p₁o ∈ affineSpan 𝕜 (Set.range s.points)) :
    ↑(s.orthogonalProjectionSpan (r₁ • (p -ᵥ ↑(s.orthogonalProjectionSpan p)) +ᵥ p₁o)) = p₁o :=
  congrArg ((↑) : _ → P) (orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ _ hp₁o)
/-
**Affine.Simplex.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProj
ection_sq** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq {
n : Nat} (s : Simplex 𝕜 P n) {p₁ : P} (p₂ : P) (hp₁ : p₁ in affineSpan 𝕜 (Set.ra
nge s.points)) : dist p₁ p₂ * dist p₁ p₂ = dist p₁ (s.orthogonalProjectionSpan p
₂) * dist p₁ (s.orthogonalProjectionSpan p₂) + dist p₂ (s.orthogonalProjectionSp
an p₂) * dist p₂ (s.orthogonalProjectionSpan p₂)
参数：s : Simplex 𝕜 P n；p₂ : P；hp₁ : p₁ in affineSpan 𝕜 (Set.range s.points)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_ortho
gonalProjection_sq`：dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalP
rojection_sq {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalPro
…
-/
theorem dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq {n : ℕ}
    (s : Simplex 𝕜 P n) {p₁ : P} (p₂ : P) (hp₁ : p₁ ∈ affineSpan 𝕜 (Set.range s.points)) :
    dist p₁ p₂ * dist p₁ p₂ =
      dist p₁ (s.orthogonalProjectionSpan p₂) * dist p₁ (s.orthogonalProjectionSpan p₂) +
        dist p₂ (s.orthogonalProjectionSpan p₂) * dist p₂ (s.orthogonalProjectionSpan p₂) :=
  EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq _ hp₁

@[simp]
/-
**Affine.Simplex.orthogonalProjectionSpan_eq_point** 是 Mathlib 中的一个引理，位于命名空间 `Af
fine.Simplex`。
形式化陈述：orthogonalProjectionSpan_eq_point (s : Simplex 𝕜 P 0) (p : P) : s.orthogon
alProjectionSpan p = s.points 0
参数：s : Simplex 𝕜 P 0；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.orthogonalProjectionSpan.eq_1`：∀ {𝕜 : Type u_1} {V : Type
 u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2
 : InnerProductSpace 𝕜 V] [inst_3 …
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.orthogonalProjection_congr`：orthogonalProjection_congr
 {s₁ s₂ : AffineSubspace 𝕜 P} {p₁ p₂ : P} [Nonempty s₁] [s₁.direction.HasOrthogo
nalProjection] (h : s₁ = s₂) (hp :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.fin_one_eq_zero`：∀ (a : Fin 1), a = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `EuclideanGeometry.orthogonalProjection_affineSpan_singleton`：∀ {𝕜 : Type
 u_1} {V : Type u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGro
up V]   [inst_2 : InnerProductSpace 𝕜 V] [inst_3 …
-/
lemma orthogonalProjectionSpan_eq_point (s : Simplex 𝕜 P 0) (p : P) :
    s.orthogonalProjectionSpan p = s.points 0 := by
  rw [orthogonalProjectionSpan]
  convert! orthogonalProjection_affineSpan_singleton _ _
  simp [Fin.fin_one_eq_zero]
/-
**Affine.Simplex.orthogonalProjectionSpan_faceOpposite_eq_point_rev** 是 Mathlib 
中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：orthogonalProjectionSpan_faceOpposite_eq_point_rev (s : Simplex 𝕜 P 1) (i 
: Fin 2) (p : P) : (s.faceOpposite i).orthogonalProjectionSpan p = s.points i.re
v
参数：s : Simplex 𝕜 P 1；i : Fin 2；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.orthogonalProjectionSpan_eq_point`：orthogonalProjectionSp
an_eq_point (s : Simplex 𝕜 P 0) (p : P) : s.orthogonalProjectionSpan p = s.point
s 0
· 使用引理 `Affine.Simplex.faceOpposite_point_eq_point_rev`：faceOpposite_point_eq_po
int_rev (s : Simplex k P 1) (i : Fin 2) (n : Fin 1) : (s.faceOpposite i).points 
n = s.points i.rev
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma orthogonalProjectionSpan_faceOpposite_eq_point_rev (s : Simplex 𝕜 P 1) (i : Fin 2)
    (p : P) : (s.faceOpposite i).orthogonalProjectionSpan p = s.points i.rev := by
  simp [faceOpposite_point_eq_point_rev]

variable [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
/-
**Affine.Simplex.orthogonalProjectionSpan_map** 是 Mathlib 中的一个引理，位于命名空间 `Affine.
Simplex`。
形式化陈述：orthogonalProjectionSpan_map {n : Nat} (s : Simplex 𝕜 P n) (f : P ->ᵃⁱ[𝕜] 
P₂) (p : P) : (s.map f.toAffineMap f.injective).orthogonalProjectionSpan (f p) =
 f (s.orthogonalProjectionSpan p)
参数：s : Simplex 𝕜 P n；f : P ->ᵃⁱ[𝕜] P₂；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.orthogonalProjection_congr`：orthogonalProjection_congr
 {s₁ s₂ : AffineSubspace 𝕜 P} {p₁ p₂ : P} [Nonempty s₁] [s₁.direction.HasOrthogo
nalProjection] (h : s₁ = s₂) (hp :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineIsometry.coe_toAffineMap`：coe_toAffineMap : ⇑f.toAffineMap = f
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EuclideanGeometry.orthogonalProjection_map`：∀ {𝕜 : Type u_1} {V : Type u
_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2 :
 InnerProductSpace 𝕜 V] {V₂ : Ty…
-/
lemma orthogonalProjectionSpan_map {n : ℕ} (s : Simplex 𝕜 P n) (f : P →ᵃⁱ[𝕜] P₂) (p : P) :
    (s.map f.toAffineMap f.injective).orthogonalProjectionSpan (f p) =
      f (s.orthogonalProjectionSpan p) := by
  simp_rw [orthogonalProjectionSpan]
  convert! orthogonalProjection_map (affineSpan 𝕜 (Set.range s.points)) f p
  simp [AffineSubspace.map_span, Set.range_comp]
/-
**Affine.Simplex.orthogonalProjectionSpan_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Af
fine.Simplex`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup V]   [inst_2 : InnerProductSpace 𝕜 V] [inst_3 : MetricSpace 
P] [inst_4 : NormedAddTorsor V P] {n : ℕ}   (s : Affine.Simplex 𝕜 P n) (S : Affi
neSubspace 𝕜 P) (hS : affineSpan 𝕜 (Set.range s.points) ≤ S) (p : ↥S),   ↑↑((s.r
estrict S hS).orthogonalProjectionSpan p) = ↑(s.orthogonalProjectionSpan ↑p)
参数：s : Affine.Simplex 𝕜 P n；S : AffineSubspace 𝕜 P；hS : affineSpan 𝕜 (Set.range 
s.points) ≤ S；p : ↥S；(s.restrict S hS).orthogonalProjectionSpan p；s.orthogonalPr
ojectionSpan ↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Affine.Simplex.orthogonalProjectionSpan_map`：orthogonalProjectionSpan_ma
p {n : Nat} (s : Simplex 𝕜 P n) (f : P ->ᵃⁱ[𝕜] P₂) (p : P) : (s.map f.toAffineMa
p f.injective).orthogonalProjecti…
-/
@[simp] lemma orthogonalProjectionSpan_restrict {n : ℕ} (s : Simplex 𝕜 P n)
    (S : AffineSubspace 𝕜 P) (hS : affineSpan 𝕜 (Set.range s.points) ≤ S) (p : S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    ((s.restrict S hS).orthogonalProjectionSpan p : P) = s.orthogonalProjectionSpan p := by
  rw [eq_comm]
  convert! (s.restrict S hS).orthogonalProjectionSpan_map S.subtypeₐᵢ p

end Simplex

end Affine

