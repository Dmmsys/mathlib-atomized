/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Affine

/-!
# Altitudes of a simplex

This file defines the altitudes of a simplex and their feet.

## Main definitions

* `altitude` is the line that passes through a vertex of a simplex and
  is orthogonal to the opposite face.

* `altitudeFoot` is the orthogonal projection of a vertex of a simplex onto the opposite face.

* `height` is the distance between a vertex of a simplex and its `altitudeFoot`.

## References

* <https://en.wikipedia.org/wiki/Altitude_(triangle)>

-/

@[expose] public section

noncomputable section

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]
variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂]
variable [NormedAddTorsor V₂ P₂]

/-- An altitude of a simplex is the line that passes through a vertex
and is orthogonal to the opposite face. -/
/-
**Affine.Simplex.altitude** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：altitude {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : AffineSubspa
ce Real P
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An altitude of a simplex is the line that passes through a vertex
and is orthogonal to the opposite face.
-/
def altitude {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) : AffineSubspace ℝ P :=
  mk' (s.points i) (affineSpan ℝ (s.points '' {i}ᶜ)).directionᗮ ⊓
    affineSpan ℝ (Set.range s.points)

/-- The definition of an altitude. -/
/-
**Affine.Simplex.altitude_def** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：altitude_def {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : s.altitu
de i = mk' (s.points i) (affineSpan Real (s.points '' {i}ᶜ)).directionᗮ ⊓ affine
Span Real (Set.range s.points)
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definition of an altitude.
-/
theorem altitude_def {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.altitude i =
      mk' (s.points i) (affineSpan ℝ (s.points '' {i}ᶜ)).directionᗮ ⊓
        affineSpan ℝ (Set.range s.points) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Affine.Simplex.altitude_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
m n : ℕ} (s : Affine.Simplex ℝ P n) (e : Fin (n + 1) ≃ Fin (m + 1)),   (s.reinde
x e).altitude = s.altitude ∘ ⇑e.symm
参数：s : Affine.Simplex ℝ P n；e : Fin (n + 1) ≃ Fin (m + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Affine.Simplex.reindex_points`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
inst_3 : AddTorsor …
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Equiv.image_compl`：∀ {α : Type u_3} {β : Type u_4} (f : α ≃ β) (s : Set 
α), ⇑f '' sᶜ = (⇑f '' s)ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Affine.Simplex.reindex_range_points`：reindex_range_points {m n : Nat} (s
 : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : Set.range (s.reindex e).poin
ts = Set.range s.points
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma altitude_reindex {m n : ℕ} (s : Simplex ℝ P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).altitude = s.altitude ∘ e.symm := by
  ext i
  simp_rw [altitude, reindex_points, Set.image_comp, Equiv.image_compl]
  simp [altitude]

/-- A vertex lies in the corresponding altitude. -/
/-
**Affine.Simplex.mem_altitude** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：mem_altitude {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : s.points
 i in s.altitude i
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AffineSubspace.mem_inf_iff`：mem_inf_iff (p : P) (s₁ s₂ : AffineSubspace 
k P) : p in s₁ ⊓ s₂ ↔ p in s₁ ∧ p in s₂
· 使用定理 `AffineSubspace.self_mem_mk'`：self_mem_mk' (p : P) (direction : Submodule
 k V) : p in mk' p direction
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
A vertex lies in the corresponding altitude.
-/
theorem mem_altitude {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.points i ∈ s.altitude i :=
  (mem_inf_iff _ _ _).2 ⟨self_mem_mk' _ _, mem_affineSpan ℝ (Set.mem_range_self _)⟩

/-- The direction of an altitude. -/
/-
**Affine.Simplex.direction_altitude** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：direction_altitude {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : (s
.altitude i).direction = (vectorSpan Real (s.points '' {i}ᶜ))ᗮ ⊓ vectorSpan Real
 (Set.range s.points)
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.altitude_def`：altitude_def {n : Nat} (s : Simplex Real P 
n) (i : Fin (n + 1)) : s.altitude i = mk' (s.points i) (affineSpan Real (s.point
s '' {i}ᶜ)).direc…
· 使用定理 `AffineSubspace.direction_inf_of_mem`：direction_inf_of_mem {s₁ s₂ : Affin
eSubspace k P} {p : P} (h₁ : p in s₁) (h₂ : p in s₂) : (s₁ ⊓ s₂).direction = s₁.
direction ⊓ s₂.direction
· 使用定理 `AffineSubspace.self_mem_mk'`：self_mem_mk' (p : P) (direction : Submodule
 k V) : p in mk' p direction
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `AffineSubspace.direction_mk'`：direction_mk' (p : P) (direction : Submodu
le k V) : (mk' p direction).direction = direction
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s

--- 原说明 ---
The direction of an altitude.
-/
theorem direction_altitude {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    (s.altitude i).direction =
      (vectorSpan ℝ (s.points '' {i}ᶜ))ᗮ ⊓ vectorSpan ℝ (Set.range s.points) := by
  rw [altitude_def,
    direction_inf_of_mem (self_mem_mk' (s.points i) _) (mem_affineSpan ℝ (Set.mem_range_self _)),
    direction_mk', direction_affineSpan, direction_affineSpan]

/-- The vector span of the opposite face lies in the direction
orthogonal to an altitude. -/
/-
**Affine.Simplex.vectorSpan_isOrtho_altitude_direction** 是 Mathlib 中的一个定理，位于命名空间
 `Affine.Simplex`。
形式化陈述：vectorSpan_isOrtho_altitude_direction {n : Nat} (s : Simplex Real P n) (i 
: Fin (n + 1)) : vectorSpan Real (s.points '' {i}ᶜ) ⟂ (s.altitude i).direction
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.direction_altitude`：direction_altitude {n : Nat} (s : Sim
plex Real P n) (i : Fin (n + 1)) : (s.altitude i).direction = (vectorSpan Real (
s.points '' {i}ᶜ))ᗮ ⊓ v…
· 使用定理 `Submodule.IsOrtho.mono_right`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RC
Like 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V₁
 V₂ : Submodule 𝕜 …
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Submodule.isOrtho_orthogonal_right`：isOrtho_orthogonal_right (U : Submod
ule 𝕜 E) : U ⟂ Uᗮ

--- 原说明 ---
The vector span of the opposite face lies in the direction
orthogonal to an altitude.
-/
theorem vectorSpan_isOrtho_altitude_direction {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    vectorSpan ℝ (s.points '' {i}ᶜ) ⟂ (s.altitude i).direction := by
  rw [direction_altitude]
  exact (Submodule.isOrtho_orthogonal_right _).mono_right inf_le_left
/-
**Affine.Simplex.altitude_map** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：altitude_map {n : Nat} (s : Simplex Real P n) (f : P ->ᵃⁱ[Real] P₂) (i : F
in (n + 1)) : (s.map f.toAffineMap f.injective).altitude i = (s.altitude i).map 
f.toAffineMap
参数：s : Simplex Real P n；f : P ->ᵃⁱ[Real] P₂；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `AffineSubspace.eq_iff_direction_eq_of_mem`：eq_iff_direction_eq_of_mem {s
₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p in s₁) (h₂ : p in s₂) : s₁ = s₂ ↔ s₁.
direction = s₂.direction
· 使用定理 `Affine.Simplex.mem_altitude`：mem_altitude {n : Nat} (s : Simplex Real P 
n) (i : Fin (n + 1)) : s.points i in s.altitude i
· 使用定理 `AffineSubspace.mem_map_of_mem`：mem_map_of_mem {x : P₁} {s : AffineSubspa
ce k P₁} (h : x in s) : f x in s.map f
· 使用定理 `LinearIsometry.injective`：∀ {R : Type u_1} {R₂ : Type u_2} {E₂ : Type u_
6} {F : Type u_9} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} 
[inst_2 : Semi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.map_direction`：map_direction (s : AffineSubspace k P₁) : 
(s.map f).direction = s.direction.map f.linear
· 使用定理 `Affine.Simplex.direction_altitude`：direction_altitude {n : Nat} (s : Sim
plex Real P n) (i : Fin (n + 1)) : (s.altitude i).direction = (vectorSpan Real (
s.points '' {i}ᶜ))ᗮ ⊓ v…
· 使用定理 `Submodule.map_inf`：map_inf (f : M ->ₛₗ[σ₁₂] M₂) {p q : Submodule R M} (h
f : Injective f) : (p ⊓ q).map f = p.map f ⊓ q.map f
· 使用定理 `AffineIsometry.linear_eq_linearIsometry`：linear_eq_linearIsometry : f.li
near = f.linearIsometry.toLinearMap
· 使用引理 `Submodule.map_orthogonal`：map_orthogonal (f : E ->ₗᵢ[𝕜] F) : Kᗮ.map f.to
LinearMap = (K.map f.toLinearMap)ᗮ ⊓ f.range
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `AffineMap.map_vectorSpan`：AffineMap.map_vectorSpan {s : Set P₁} : Submod
ule.map f.linear (vectorSpan k s) = vectorSpan k (f '' s)
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
-/
lemma altitude_map {n : ℕ} (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).altitude i = (s.altitude i).map f.toAffineMap := by
  refine (eq_iff_direction_eq_of_mem (p := f (s.points i)) ?_ ?_).mpr ?_
  · exact (s.map f.toAffineMap f.injective).mem_altitude i
  · exact mem_map_of_mem f.toAffineMap (s.mem_altitude i)
  have hf : Function.Injective f.linear := f.linearIsometry.injective
  rw [map_direction, direction_altitude, direction_altitude, Submodule.map_inf _ hf,
    AffineIsometry.linear_eq_linearIsometry, Submodule.map_orthogonal,
    ← AffineIsometry.linear_eq_linearIsometry, map_points, Set.range_comp,
    Set.image_comp, ← AffineMap.map_vectorSpan, inf_assoc, ← Submodule.map_top,
    ← Submodule.map_inf _ hf, top_inf_eq, ← AffineMap.map_vectorSpan]
/-
**Affine.Simplex.map_altitude_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex
`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} (s : Affine.Simplex ℝ P n) (S : AffineSubspace ℝ P)   (hS : affineSpan ℝ 
(Set.range s.points) ≤ S) (i : Fin (n + 1)),   AffineSubspace.map S.subtype ((s.
restrict S hS).altitude i) = s.altitude i
参数：s : Affine.Simplex ℝ P n；S : AffineSubspace ℝ P；hS : affineSpan ℝ (Set.range 
s.points) ≤ S；i : Fin (n + 1)；(s.restrict S hS).altitude i。
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
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `Affine.Simplex.altitude_map`：altitude_map {n : Nat} (s : Simplex Real P 
n) (f : P ->ᵃⁱ[Real] P₂) (i : Fin (n + 1)) : (s.map f.toAffineMap f.injective).a
ltitude i = (s.al…
-/
@[simp] lemma map_altitude_restrict {n : ℕ} (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    ((s.restrict S hS).altitude i).map S.subtype = s.altitude i := by
  rw [eq_comm]
  convert! (s.restrict S hS).altitude_map S.subtypeₐᵢ i
/-
**Affine.Simplex.altitude_restrict_eq_comap_subtype** 是 Mathlib 中的一个引理，位于命名空间 `A
ffine.Simplex`。
形式化陈述：altitude_restrict_eq_comap_subtype {n : Nat} (s : Simplex Real P n) (S : A
ffineSubspace Real P) (hS : affineSpan Real (Set.range s.points) <= S) (i : Fin 
(n + 1)) : haveI
参数：s : Simplex Real P n；S : AffineSubspace Real P；hS : affineSpan Real (Set.rang
e s.points) <= S；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.map_altitude_restrict`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用引理 `AffineSubspace.comap_map_eq_of_injective`：comap_map_eq_of_injective {f :
 P₁ ->ᵃ[k] P₂} (hf : Function.Injective f) (s : AffineSubspace k P₁) : (s.map f)
.comap f = s
· 使用定理 `AffineSubspace.subtype_injective`：subtype_injective (s : AffineSubspace 
k P) [Nonempty s] : Function.Injective s.subtype
-/
lemma altitude_restrict_eq_comap_subtype {n : ℕ} (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).altitude i = (s.altitude i).comap S.subtype := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  rw [← s.map_altitude_restrict S hS, comap_map_eq_of_injective S.subtype_injective]

open Module

/-- An altitude is finite-dimensional. -/
/-
**Affine.Simplex.finiteDimensional_direction_altitude** 是 Mathlib 中的一个实例，位于命名空间 
`Affine.Simplex`。
形式化陈述：finiteDimensional_direction_altitude {n : Nat} (s : Simplex Real P n) (i :
 Fin (n + 1)) : FiniteDimensional Real (s.altitude i).direction
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.direction_altitude`：direction_altitude {n : Nat} (s : Sim
plex Real P n) (i : Fin (n + 1)) : (s.altitude i).direction = (vectorSpan Real (
s.points '' {i}ᶜ))ᗮ ⊓ v…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
An altitude is finite-dimensional.
-/
instance finiteDimensional_direction_altitude {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    FiniteDimensional ℝ (s.altitude i).direction := by
  rw [direction_altitude]
  infer_instance

/-- An altitude is one-dimensional (i.e., a line). -/
@[simp]
/-
**Affine.Simplex.finrank_direction_altitude** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Si
mplex`。
形式化陈述：finrank_direction_altitude {n : Nat} [NeZero n] (s : Simplex Real P n) (i 
: Fin (n + 1)) : finrank Real (s.altitude i).direction = 1
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.direction_altitude`：direction_altitude {n : Nat} (s : Sim
plex Real P n) (i : Fin (n + 1)) : (s.altitude i).direction = (vectorSpan Real (
s.points '' {i}ᶜ))ᗮ ⊓ v…
· 使用定理 `Submodule.finrank_add_inf_finrank_orthogonal`：finrank_add_inf_finrank_or
thogonal {K₁ K₂ : Submodule 𝕜 E} [FiniteDimensional 𝕜 K₂] (h : K₁ <= K₂) : finra
nk 𝕜 K₁ + finrank 𝕜 (K₁ᗮ ⊓ K₂ : Su…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `vectorSpan_mono`：vectorSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
vectorSpan k s₁ <= vectorSpan k s₂
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `AffineIndependent.finrank_vectorSpan`：AffineIndependent.finrank_vectorSp
an [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p) {n : Nat} (hc : Fintype
.card ι = n + 1) : finrank…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Finset.coe_compl`：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `AffineIndependent.finrank_vectorSpan_image_finset`：AffineIndependent.fin
rank_vectorSpan_image_finset [DecidableEq P] {p : ι -> P} (hi : AffineIndependen
t k p) {s : Finset ι} {n : Nat} (hc : #…

--- 原说明 ---
An altitude is one-dimensional (i.e., a line).
-/
theorem finrank_direction_altitude {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    finrank ℝ (s.altitude i).direction = 1 := by
  rw [direction_altitude]
  have h := Submodule.finrank_add_inf_finrank_orthogonal
    (vectorSpan_mono ℝ (Set.image_subset_range s.points {i}ᶜ))
  have hn : (n - 1) + 1 = n := by
    have := NeZero.ne n
    cases n <;> lia
  have hc : #({i}ᶜ) = (n - 1) + 1 := by
    rw [card_compl, card_singleton, Fintype.card_fin, hn, add_tsub_cancel_right]
  refine add_left_cancel (_root_.trans h ?_)
  classical
  rw [s.independent.finrank_vectorSpan (Fintype.card_fin _), ← Finset.coe_singleton,
    ← Finset.coe_compl, ← Finset.coe_image,
    s.independent.finrank_vectorSpan_image_finset hc, hn]

/-- A line through a vertex is the altitude through that vertex if and
only if it is orthogonal to the opposite face. -/
/-
**Affine.Simplex.affineSpan_pair_eq_altitude_iff** 是 Mathlib 中的一个定理，位于命名空间 `Affi
ne.Simplex`。
形式化陈述：affineSpan_pair_eq_altitude_iff {n : Nat} [NeZero n] (s : Simplex Real P n
) (i : Fin (n + 1)) (p : P) : line[Real, p, s.points i] = s.altitude i ↔ p != s.
points i ∧ p in affineSpan Real (Set.range s.points) ∧ p -ᵥ s.points i in (affin
eSpan Real (s.points '' {i}ᶜ)).directionᗮ
参数：s : Simplex Real P n；i : Fin (n + 1)；p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.eq_iff_direction_eq_of_mem`：eq_iff_direction_eq_of_mem {s
₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p in s₁) (h₂ : p in s₂) : s₁ = s₂ ↔ s₁.
direction = s₂.direction
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Affine.Simplex.mem_altitude`：mem_altitude {n : Nat} (s : Simplex Real P 
n) (i : Fin (n + 1)) : s.points i in s.altitude i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.vsub_right_mem_direction_iff_mem`：vsub_right_mem_directio
n_iff_mem {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P) : p₂ -ᵥ p in s
.direction ↔ p₂ in s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `vectorSpan_singleton`：vectorSpan_singleton (p : P) : vectorSpan k ({p} :
 Set P) = ⊥
· 使用定理 `Set.pair_eq_singleton`：pair_eq_singleton (a : α) : ({a, a} : Set α) = {a
}
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Affine.Simplex.finrank_direction_altitude`：finrank_direction_altitude {n
 : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) : finrank Real (s.al
titude i).direction = 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Submodule.mem_inf`：mem_inf {p q : Submodule R M} {x : M} : x in p ⊓ q ↔ 
x in p ∧ x in q
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Affine.Simplex.direction_altitude`：direction_altitude {n : Nat} (s : Sim
plex Real P n) (i : Fin (n + 1)) : (s.altitude i).direction = (vectorSpan Real (
s.points '' {i}ᶜ))ᗮ ⊓ v…
· 使用定理 `vsub_mem_vectorSpan`：vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : 
p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in vectorSpan k s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `vectorSpan_eq_span_vsub_set_left_ne`：vectorSpan_eq_span_vsub_set_left_ne
 {s : Set P} {p : P} (hp : p in s) : vectorSpan k s = Submodule.span k ((p -ᵥ ·)
 '' (s \ {p}))
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Submodule.eq_of_le_of_finrank_eq`：eq_of_le_of_finrank_eq {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₁ = finrank 
K S₂) : S₁ = S₂
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
A line through a vertex is the altitude through that vertex if and
only if it is orthogonal to the opposite face.
-/
theorem affineSpan_pair_eq_altitude_iff {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1))
    (p : P) :
    line[ℝ, p, s.points i] = s.altitude i ↔
      p ≠ s.points i ∧
        p ∈ affineSpan ℝ (Set.range s.points) ∧
          p -ᵥ s.points i ∈ (affineSpan ℝ (s.points '' {i}ᶜ)).directionᗮ := by
  rw [eq_iff_direction_eq_of_mem (mem_affineSpan ℝ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (s.mem_altitude _),
    ← vsub_right_mem_direction_iff_mem (mem_affineSpan ℝ (Set.mem_range_self i)) p,
    direction_affineSpan, direction_affineSpan, direction_affineSpan]
  constructor
  · intro h
    constructor
    · intro heq
      rw [heq, Set.pair_eq_singleton, vectorSpan_singleton] at h
      have hd : finrank ℝ (s.altitude i).direction = 0 := by rw [← h, finrank_bot]
      simp at hd
    · rw [← Submodule.mem_inf, _root_.inf_comm, ← direction_altitude, ← h]
      exact
        vsub_mem_vectorSpan ℝ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · rintro ⟨hne, h⟩
    rw [← Submodule.mem_inf, _root_.inf_comm, ← direction_altitude] at h
    rw [vectorSpan_eq_span_vsub_set_left_ne ℝ (Set.mem_insert _ _),
      Set.insert_sdiff_of_mem _ (Set.mem_singleton _),
      Set.sdiff_singleton_eq_self fun h => hne (Set.mem_singleton_iff.1 h), Set.image_singleton]
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      simpa using h
    · rw [finrank_direction_altitude, finrank_span_set_eq_card]
      · simp
      · exact .singleton <| by simpa using hne

/-- The foot of an altitude is the orthogonal projection of a vertex of a simplex onto the
opposite face. -/
/-
**Affine.Simplex.altitudeFoot** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：altitudeFoot {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1))
 : P
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The foot of an altitude is the orthogonal projection of a vertex of a simplex on
to the
opposite face.
-/
def altitudeFoot {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) : P :=
  (s.faceOpposite i).orthogonalProjectionSpan (s.points i)
/-
**Affine.Simplex.altitudeFoot_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`
。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
m n : ℕ} [inst_4 : NeZero m] [inst_5 : NeZero n] (s : Affine.Simplex ℝ P n)   (e
 : Fin (n + 1) ≃ Fin (m + 1)), (s.reindex e).altitudeFoot = s.altitudeFoot ∘ ⇑e.
symm
参数：s : Affine.Simplex ℝ P n；e : Fin (n + 1) ≃ Fin (m + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.reindex_points`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
inst_3 : AddTorsor …
· 使用引理 `Affine.Simplex.orthogonalProjectionSpan_congr`：orthogonalProjectionSpan_
congr {m n : Nat} {s₁ : Simplex 𝕜 P m} {s₂ : Simplex 𝕜 P n} {p₁ p₂ : P} (h : Set
.range s₁.points = Set.range s₂.poi…
· 使用引理 `Affine.Simplex.range_faceOpposite_reindex`：range_faceOpposite_reindex {m
 n : Nat} [NeZero m] [NeZero n] (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 
1)) (i : Fin (n + 1)) : Set.ran…
-/
@[simp] lemma altitudeFoot_reindex {m n : ℕ} [NeZero m] [NeZero n] (s : Simplex ℝ P n)
    (e : Fin (n + 1) ≃ Fin (m + 1)) : (s.reindex e).altitudeFoot = s.altitudeFoot ∘ e.symm := by
  ext i
  simp only [altitudeFoot, reindex_points, Function.comp_apply]
  exact orthogonalProjectionSpan_congr (s.range_faceOpposite_reindex e i) rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Affine.Simplex.altitudeFoot_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
V₂ : Type u_3} {P₂ : Type u_4} [inst_4 : NormedAddCommGroup V₂]   [inst_5 : Inne
rProductSpace ℝ V₂] [inst_6 : MetricSpace P₂] [inst_7 : NormedAddTorsor V₂ P₂] {
n : ℕ}   [inst_8 : NeZero n] (s : Affine.Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) (i : F
in (n + 1)),   (s.map f.toAffineMap ⋯).altitudeFoot i = f (s.altitudeFoot i)
参数：s : Affine.Simplex ℝ P n；f : P →ᵃⁱ[ℝ] P₂；i : Fin (n + 1)；s.map f.toAffineMap 
⋯；s.altitudeFoot i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineIsometry.coe_toAffineMap`：coe_toAffineMap : ⇑f.toAffineMap = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma altitudeFoot_map {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂)
    (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).altitudeFoot i = f (s.altitudeFoot i) := by
  simp [altitudeFoot, ← orthogonalProjectionSpan_map]
/-
**Affine.Simplex.altitudeFoot_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex
`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (S : AffineSubspace ℝ P)  
 (hS : affineSpan ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)), ↑((s.restrict S
 hS).altitudeFoot i) = s.altitudeFoot i
参数：s : Affine.Simplex ℝ P n；S : AffineSubspace ℝ P；hS : affineSpan ℝ (Set.range 
s.points) ≤ S；i : Fin (n + 1)；(s.restrict S hS).altitudeFoot i。
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
· 使用定理 `Affine.Simplex.altitudeFoot_map`：∀ {V : Type u_1} {P : Type u_2} [inst :
 NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]
   [inst_3 : NormedAd…
-/
@[simp] lemma altitudeFoot_restrict {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).altitudeFoot i = s.altitudeFoot i := by
  rw [eq_comm]
  convert! (s.restrict S hS).altitudeFoot_map S.subtypeₐᵢ i
/-
**Affine.Simplex.ne_altitudeFoot** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (i : Fin (n + 1)),   s.poi
nts i ≠ s.altitudeFoot i
参数：s : Affine.Simplex ℝ P n；i : Fin (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `EuclideanGeometry.orthogonalProjection_eq_self_iff`：orthogonalProjection
_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalPro
jection] {p : P} : ↑(orthogonalProjectio…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Affine.Simplex.orthogonalProjectionSpan.eq_1`：∀ {𝕜 : Type u_1} {V : Type
 u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2
 : InnerProductSpace 𝕜 V] [inst_3 …
· 使用定理 `Affine.Simplex.altitudeFoot.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst 
: NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P
]   [inst_3 : NormedAd…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
@[simp] lemma ne_altitudeFoot {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.points i ≠ s.altitudeFoot i := by
  intro h
  rw [eq_comm, altitudeFoot, orthogonalProjectionSpan, orthogonalProjection_eq_self_iff] at h
  simp at h
/-
**Affine.Simplex.altitudeFoot_mem_affineSpan_image_compl** 是 Mathlib 中的一个定理，位于命名
空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (i : Fin (n + 1)),   s.alt
itudeFoot i ∈ affineSpan ℝ (s.points '' {i}ᶜ)
参数：s : Affine.Simplex ℝ P n；i : Fin (n + 1)；s.points '' {i}ᶜ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
-/
@[simp] lemma altitudeFoot_mem_affineSpan_image_compl {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) : s.altitudeFoot i ∈ affineSpan ℝ (s.points '' {i}ᶜ) := by
  rw [← range_faceOpposite_points]
  exact orthogonalProjection_mem _
/-
**Affine.Simplex.altitudeFoot_mem_affineSpan_faceOpposite** 是 Mathlib 中的一个引理，位于命
名空间 `Affine.Simplex`。
形式化陈述：altitudeFoot_mem_affineSpan_faceOpposite {n : Nat} [NeZero n] (s : Simplex
 Real P n) (i : Fin (n + 1)) : s.altitudeFoot i in affineSpan Real (Set.range (s
.faceOpposite i).points)
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
-/
lemma altitudeFoot_mem_affineSpan_faceOpposite {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) : s.altitudeFoot i ∈ affineSpan ℝ (Set.range (s.faceOpposite i).points) :=
  orthogonalProjection_mem _
/-
**Affine.Simplex.altitudeFoot_mem_affineSpan** 是 Mathlib 中的一个引理，位于命名空间 `Affine.S
implex`。
形式化陈述：altitudeFoot_mem_affineSpan {n : Nat} [NeZero n] (s : Simplex Real P n) (i
 : Fin (n + 1)) : s.altitudeFoot i in affineSpan Real (Set.range s.points)
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用引理 `Affine.Simplex.altitudeFoot_mem_affineSpan_faceOpposite`：altitudeFoot_me
m_affineSpan_faceOpposite {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (
n + 1)) : s.altitudeFoot i in affineSpan Real…
-/
lemma altitudeFoot_mem_affineSpan {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (i : Fin (n + 1)) : s.altitudeFoot i ∈ affineSpan ℝ (Set.range s.points) := by
  refine SetLike.le_def.1 (affineSpan_mono _ ?_) (s.altitudeFoot_mem_affineSpan_faceOpposite _)
  simp
/-
**Affine.Simplex.affineSpan_pair_altitudeFoot_eq_altitude** 是 Mathlib 中的一个引理，位于命
名空间 `Affine.Simplex`。
形式化陈述：affineSpan_pair_altitudeFoot_eq_altitude {n : Nat} [NeZero n] (s : Simplex
 Real P n) (i : Fin (n + 1)) : line[Real, s.altitudeFoot i, s.points i] = s.alti
tude i
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.affineSpan_pair_eq_altitude_iff`：affineSpan_pair_eq_altit
ude_iff {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) (p : P) : 
line[Real, p, s.points i] = s.altitu…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Affine.Simplex.ne_altitudeFoot`：∀ {V : Type u_1} {P : Type u_2} [inst : 
NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] 
  [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.altitudeFoot_mem_affineSpan`：altitudeFoot_mem_affineSpan 
{n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) : s.altitudeFoot i
 in affineSpan Real (Set.range s…
· 使用定理 `Affine.Simplex.altitudeFoot.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst 
: NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P
]   [inst_3 : NormedAd…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Affine.Simplex.orthogonalProjectionSpan.eq_1`：∀ {𝕜 : Type u_1} {V : Type
 u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2
 : InnerProductSpace 𝕜 V] [inst_3 …
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EuclideanGeometry.orthogonalProjection_congr`：orthogonalProjection_congr
 {s₁ s₂ : AffineSubspace 𝕜 P} {p₁ p₂ : P} [Nonempty s₁] [s₁.direction.HasOrthogo
nalProjection] (h : s₁ = s₂) (hp :…
· 使用定理 `EuclideanGeometry.orthogonalProjection_vsub_mem_direction_orthogonal`：or
thogonalProjection_vsub_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : (or…
-/
lemma affineSpan_pair_altitudeFoot_eq_altitude
    {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    line[ℝ, s.altitudeFoot i, s.points i] = s.altitude i := by
  rw [affineSpan_pair_eq_altitude_iff]
  refine ⟨(s.ne_altitudeFoot i).symm, s.altitudeFoot_mem_affineSpan _, ?_⟩
  rw [altitudeFoot, orthogonalProjectionSpan]
  simp_rw [range_faceOpposite_points]
  exact orthogonalProjection_vsub_mem_direction_orthogonal _ _
/-
**Affine.Simplex.altitudeFoot_mem_altitude** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Sim
plex`。
形式化陈述：altitudeFoot_mem_altitude {n : Nat} [NeZero n] (s : Simplex Real P n) (i :
 Fin (n + 1)) : s.altitudeFoot i in s.altitude i
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Affine.Simplex.affineSpan_pair_altitudeFoot_eq_altitude`：affineSpan_pair
_altitudeFoot_eq_altitude {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (
n + 1)) : line[Real, s.altitudeFoot i, s.poin…
· 使用定理 `left_mem_affineSpan_pair`：left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in l
ine[k, p₁, p₂]
-/
lemma altitudeFoot_mem_altitude {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.altitudeFoot i ∈ s.altitude i := by
  rw [← affineSpan_pair_altitudeFoot_eq_altitude]
  exact left_mem_affineSpan_pair _ _ _
/-
**Affine.Simplex.altitudeFoot_eq_point_rev** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Sim
plex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : Affine.Simplex ℝ P 1) (i : Fin 2), s.altitudeFoot i = s.points i.rev
参数：s : Affine.Simplex ℝ P 1；i : Fin 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Affine.Simplex.orthogonalProjectionSpan_eq_point`：orthogonalProjectionSp
an_eq_point (s : Simplex 𝕜 P 0) (p : P) : s.orthogonalProjectionSpan p = s.point
s 0
· 使用引理 `Affine.Simplex.faceOpposite_point_eq_point_rev`：faceOpposite_point_eq_po
int_rev (s : Simplex k P 1) (i : Fin 2) (n : Fin 1) : (s.faceOpposite i).points 
n = s.points i.rev
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma altitudeFoot_eq_point_rev (s : Simplex ℝ P 1) (i : Fin 2) :
    s.altitudeFoot i = s.points i.rev := by
  simp [altitudeFoot, faceOpposite_point_eq_point_rev]

/-- The height of a vertex of a simplex is the distance between it and the foot of the altitude
from that vertex. -/
/-
**Affine.Simplex.height** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：height {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) : Rea
l
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The height of a vertex of a simplex is the distance between it and the foot of t
he altitude
from that vertex.
-/
def height {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) : ℝ :=
  dist (s.points i) (s.altitudeFoot i)
/-
**Affine.Simplex.height_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
m n : ℕ} [inst_4 : NeZero m] [inst_5 : NeZero n] (s : Affine.Simplex ℝ P n)   (e
 : Fin (n + 1) ≃ Fin (m + 1)), (s.reindex e).height = s.height ∘ ⇑e.symm
参数：s : Affine.Simplex ℝ P n；e : Fin (n + 1) ≃ Fin (m + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Affine.Simplex.reindex_points`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
inst_3 : AddTorsor …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.altitudeFoot_reindex`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma height_reindex {m n : ℕ} [NeZero m] [NeZero n] (s : Simplex ℝ P n)
    (e : Fin (n + 1) ≃ Fin (m + 1)) : (s.reindex e).height = s.height ∘ e.symm := by
  ext i
  simp [height]
/-
**Affine.Simplex.height_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
V₂ : Type u_3} {P₂ : Type u_4} [inst_4 : NormedAddCommGroup V₂]   [inst_5 : Inne
rProductSpace ℝ V₂] [inst_6 : MetricSpace P₂] [inst_7 : NormedAddTorsor V₂ P₂] {
n : ℕ}   [inst_8 : NeZero n] (s : Affine.Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) (i : F
in (n + 1)),   (s.map f.toAffineMap ⋯).height i = s.height i
参数：s : Affine.Simplex ℝ P n；f : P →ᵃⁱ[ℝ] P₂；i : Fin (n + 1)；s.map f.toAffineMap 
⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `AffineIsometry.coe_toAffineMap`：coe_toAffineMap : ⇑f.toAffineMap = f
· 使用定理 `Affine.Simplex.altitudeFoot_map`：∀ {V : Type u_1} {P : Type u_2} [inst :
 NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]
   [inst_3 : NormedAd…
· 使用定理 `AffineIsometry.dist_map`：dist_map (x y : P) : dist (f x) (f y) = dist x 
y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma height_map {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂)
    (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).height i = s.height i := by
  simp [height]
/-
**Affine.Simplex.height_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (S : AffineSubspace ℝ P)  
 (hS : affineSpan ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)), (s.restrict S h
S).height i = s.height i
参数：s : Affine.Simplex ℝ P n；S : AffineSubspace ℝ P；hS : affineSpan ℝ (Set.range 
s.points) ≤ S；i : Fin (n + 1)；s.restrict S hS。
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
· 使用定理 `Affine.Simplex.height_map`：∀ {V : Type u_1} {P : Type u_2} [inst : Norme
dAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [in
st_3 : NormedAd…
-/
@[simp] lemma height_restrict {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).height i = s.height i := by
  rw [eq_comm]
  convert! (s.restrict S hS).height_map S.subtypeₐᵢ i

@[simp]
/-
**Affine.Simplex.height_pos** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：height_pos {n : Nat} [NeZero n] (s : Simplex Real P n) (i : Fin (n + 1)) :
 0 < s.height i
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma height_pos {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) : 0 < s.height i := by
  simp [height]

open Qq Mathlib.Meta.Positivity in
/-- Extension for the `positivity` tactic: the height of a simplex is always positive. -/
@[positivity height _ _]
meta def evalHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@height $V $P $i1 $i2 $i3 $i4 $n $hn $s $i) =>
    assertInstancesCommute
    return .positive q(height_pos $s $i)
  | _, _, _ => throwError "not Simplex.height"

/-
**Affine.Simplex.** 是 Mathlib 中的一个示例，位于命名空间 `Affine.Simplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) : 0 < s.height i := by
  positivity

/-- The height of a 1-dimensional simplex equals to the distance between the two vertices. -/
/-
**Affine.Simplex.height_eq_dist** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : Affine.Simplex ℝ P 1) (i : Fin 2), s.height i = dist (s.points 0) (s.points 
1)
参数：s : Affine.Simplex ℝ P 1；i : Fin 2；s.points 0；s.points 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.altitudeFoot_eq_point_rev`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…
· 使用定理 `Fin.rev_zero`：∀ (n : ℕ), Fin.rev 0 = Fin.last n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
The height of a 1-dimensional simplex equals to the distance between the two ver
tices.
-/
@[simp] lemma height_eq_dist (s : Simplex ℝ P 1) (i : Fin 2) :
    s.height i = dist (s.points 0) (s.points 1) := by
  fin_cases i
  · simp [height]
  · rw [dist_comm]
    simp [height]

open scoped RealInnerProductSpace

variable {n : ℕ} (s : Simplex ℝ P n)

/-- Altitudes are perpendicular to the faces containing their foot. -/
/-
**Affine.Simplex.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero** 是 Mathlib 中
的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero {i j : Fin (n + 1)} (h :
 i != j) : have : NeZero n
参数：n + 1；h : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.inner_right_of_mem_orthogonal`：inner_right_of_mem_orthogonal {
u v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪u, v⟫ = 0
· 使用定理 `vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan`：vsub_mem_vector
Span_of_mem_affineSpan_of_mem_affineSpan {s : Set P} {p₁ p₂ : P} (hp₁ : p₁ in af
fineSpan k s) (hp₂ : p₂ in affineSpan k s) : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Affine.Simplex.mem_affineSpan_image_iff`：∀ {k : Type u_1} {V : Type u_2}
 {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modul
e k V]   [inst_3 : AddTorsor …
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Affine.Simplex.altitudeFoot_mem_affineSpan_image_compl`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal`：vs
ub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : p -…

--- 原说明 ---
Altitudes are perpendicular to the faces containing their foot.
-/
lemma inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero {i j : Fin (n + 1)} (h : i ≠ j) :
    have : NeZero n := by grind [neZero_iff]
    ⟪s.points j -ᵥ s.altitudeFoot i, s.points i -ᵥ s.altitudeFoot i⟫ = 0 := by
  have : NeZero n := by grind [neZero_iff]
  refine Submodule.inner_right_of_mem_orthogonal
    (K := vectorSpan ℝ (s.points '' {i}ᶜ))
    (vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (s.mem_affineSpan_image_iff.2 h.symm)
      (Affine.Simplex.altitudeFoot_mem_affineSpan_image_compl _ _))
    ?_
  rw [← direction_affineSpan, ← Affine.Simplex.range_faceOpposite_points]
  exact vsub_orthogonalProjection_mem_direction_orthogonal _ _

/-- The inner product of an edge from `j` to `i` and the vector from the foot of `i` to `i`
is the square of the height. -/
/-
**Affine.Simplex.inner_vsub_vsub_altitudeFoot_eq_height_sq** 是 Mathlib 中的一个引理，位于
命名空间 `Affine.Simplex`。
形式化陈述：inner_vsub_vsub_altitudeFoot_eq_height_sq [NeZero n] {i j : Fin (n + 1)} (
h : i != j) : ⟪s.points i -ᵥ s.points j, s.points i -ᵥ s.altitudeFoot i⟫ = s.hei
ght i ^ 2
参数：n + 1；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero`：inner_
vsub_altitudeFoot_vsub_altitudeFoot_eq_zero {i j : Fin (n + 1)} (h : i != j) : h
ave : NeZero n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.height.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : Norm
edAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [i
nst_3 : NormedAd…
· 使用定理 `inner_vsub_vsub_left_eq_dist_sq_right_iff`：inner_vsub_vsub_left_eq_dist_
sq_right_iff {a b c : P} : ⟪a -ᵥ b, a -ᵥ c⟫ = dist a c ^ 2 ↔ ⟪c -ᵥ b, a -ᵥ c⟫ = 
0
· 使用定理 `inner_vsub_left_eq_zero_symm`：inner_vsub_left_eq_zero_symm {a b : P} {v 
: V} : ⟪a -ᵥ b, v⟫_𝕜 = 0 ↔ ⟪b -ᵥ a, v⟫_𝕜 = 0

--- 原说明 ---
The inner product of an edge from `j` to `i` and the vector from the foot of `i`
 to `i`
is the square of the height.
-/
lemma inner_vsub_vsub_altitudeFoot_eq_height_sq [NeZero n] {i j : Fin (n + 1)} (h : i ≠ j) :
    ⟪s.points i -ᵥ s.points j, s.points i -ᵥ s.altitudeFoot i⟫ = s.height i ^ 2 := by
  suffices ⟪s.points j -ᵥ s.altitudeFoot i, s.points i -ᵥ s.altitudeFoot i⟫ = 0 by
    rwa [height, inner_vsub_vsub_left_eq_dist_sq_right_iff, inner_vsub_left_eq_zero_symm]
  exact s.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero h

variable [Nat.AtLeastTwo n]

/--
The inner product of two distinct altitudes has absolute value strictly less than the product of
their lengths.

Equivalently, neither vector is a multiple of the other; the angle between them is not 0 or π. -/
/-
**Affine.Simplex.abs_inner_vsub_altitudeFoot_lt_mul** 是 Mathlib 中的一个引理，位于命名空间 `A
ffine.Simplex`。
形式化陈述：abs_inner_vsub_altitudeFoot_lt_mul {i j : Fin (n + 1)} (hij : i != j) : |⟪
s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫| < s.height i * 
s.height j
参数：n + 1；hij : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `abs_real_inner_le_norm`：abs_real_inner_le_norm (x y : F) : |⟪x, y⟫_Real|
 <= ‖x‖ * ‖y‖
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `norm_inner_eq_norm_iff`：norm_inner_eq_norm_iff {x y : E} (hx₀ : x != 0) 
(hy₀ : y != 0) : ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ exists r : 𝕜, r != 0 ∧ y = r • x
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Submodule.inf_orthogonal_eq_bot`：inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥
· 使用定理 `vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan`：vsub_mem_vector
Span_of_mem_affineSpan_of_mem_affineSpan {s : Set P} {p₁ p₂ : P} (hp₁ : p₁ in af
fineSpan k s) (hp₂ : p₂ in affineSpan k s) : …
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Fin.exists_ne_and_ne_of_two_lt`：exists_ne_and_ne_of_two_lt (i j : Fin n)
 (h : 2 < n) : exists k, k != i ∧ k != j
（共 82 条，此处仅展示前 30 条）

--- 原说明 ---
The inner product of two distinct altitudes has absolute value strictly less tha
n the product of
their lengths.

Equivalently, neither vector is a multiple of the other; the angle between them 
is not 0 or π.
-/
lemma abs_inner_vsub_altitudeFoot_lt_mul {i j : Fin (n + 1)} (hij : i ≠ j) :
    |⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫|
      < s.height i * s.height j := by
  apply lt_of_le_of_ne
  · convert! abs_real_inner_le_norm _ _ using 1
    simp only [dist_eq_norm_vsub, height]
  · simp_rw [height, dist_eq_norm_vsub]
    rw [← Real.norm_eq_abs, ne_eq, norm_inner_eq_norm_iff (by simp) (by simp)]
    rintro ⟨r, hr, h⟩
    suffices s.points j -ᵥ s.altitudeFoot j = 0 by
      simp at this
    rw [← Submodule.mem_bot ℝ,
      ← Submodule.inf_orthogonal_eq_bot (vectorSpan ℝ (Set.range s.points))]
    refine ⟨vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
      (mem_affineSpan _ (Set.mem_range_self _)) ?_, ?_⟩
    · refine SetLike.le_def.1 (affineSpan_mono _ ?_) (Subtype.property _)
      simp
    · rw [SetLike.mem_coe]
      have hk : ∃ k, k ≠ i ∧ k ≠ j := Fin.exists_ne_and_ne_of_two_lt i j
        (by linarith only [Nat.AtLeastTwo.one_lt (n := n)])
      have hs : vectorSpan ℝ (Set.range s.points) =
          vectorSpan ℝ (Set.range (s.faceOpposite i).points) ⊔
            vectorSpan ℝ (Set.range (s.faceOpposite j).points) := by
        rcases hk with ⟨k, hki, hkj⟩
        have hki' : s.points k ∈ Set.range (s.faceOpposite i).points := by
          rw [range_faceOpposite_points]
          exact Set.mem_image_of_mem _ hki
        have hkj' : s.points k ∈ Set.range (s.faceOpposite j).points := by
          rw [range_faceOpposite_points]
          exact Set.mem_image_of_mem _ hkj
        have hs :
            Set.range s.points =
              Set.range (s.faceOpposite i).points ∪ Set.range (s.faceOpposite j).points := by
          simp only [range_faceOpposite_points, ← Set.image_union]
          simp_rw [← Set.image_univ, ← Set.compl_inter]
          rw [Set.inter_singleton_eq_empty.mpr ?_, Set.compl_empty]
          simpa using hij.symm
        convert! AffineSubspace.vectorSpan_union_of_mem_of_mem ℝ hki' hkj'
      rw [hs, ← Submodule.inf_orthogonal, Submodule.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [h, ← direction_affineSpan]
        exact Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal _ _)
      · rw [← direction_affineSpan]
        exact vsub_orthogonalProjection_mem_direction_orthogonal _ _

/--
The inner product of two altitudes has value strictly greater than the negated product of
their lengths.
-/
/-
**Affine.Simplex.neg_mul_lt_inner_vsub_altitudeFoot** 是 Mathlib 中的一个引理，位于命名空间 `A
ffine.Simplex`。
形式化陈述：neg_mul_lt_inner_vsub_altitudeFoot (i j : Fin (n + 1)) : -(s.height i * s.
height j) < ⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫
参数：i j : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_self_eq_norm_sq`：real_inner_self_eq_norm_sq (x : F) : ⟪x, x⟫_
Real = ‖x‖ ^ 2
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Affine.Simplex.height_pos`：height_pos {n : Nat} [NeZero n] (s : Simplex 
Real P n) (i : Fin (n + 1)) : 0 < s.height i
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `neg_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStric
tMono α] {a b : α} [AddRightStrictMono α],   -a < b ↔ -b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `lt_of_abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder
 α] {a b : α}, |a| < b → a < b
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用引理 `Affine.Simplex.abs_inner_vsub_altitudeFoot_lt_mul`：abs_inner_vsub_altitu
deFoot_lt_mul {i j : Fin (n + 1)} (hij : i != j) : |⟪s.points i -ᵥ s.altitudeFoo
t i, s.points j -ᵥ s.altitudeFoot j⟫| <…

--- 原说明 ---
The inner product of two altitudes has value strictly greater than the negated p
roduct of
their lengths.
-/
lemma neg_mul_lt_inner_vsub_altitudeFoot (i j : Fin (n + 1)) :
    -(s.height i * s.height j)
      < ⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫ := by
  obtain rfl | hij := eq_or_ne i j
  · rw [real_inner_self_eq_norm_sq]
    refine lt_of_lt_of_le (b := 0) ?_ ?_
    · rw [neg_lt_zero]
      positivity
    · positivity
  rw [neg_lt]
  refine lt_of_abs_lt ?_
  rw [abs_neg]
  exact abs_inner_vsub_altitudeFoot_lt_mul s hij
/-
**Affine.Simplex.abs_inner_vsub_altitudeFoot_div_lt_one** 是 Mathlib 中的一个引理，位于命名空
间 `Affine.Simplex`。
形式化陈述：abs_inner_vsub_altitudeFoot_div_lt_one {i j : Fin (n + 1)} (hij : i != j) 
: |⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫ / (s.height 
i * s.height j)| < 1
参数：n + 1；hij : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `abs_dist`：∀ {α : Type u} [inst : PseudoMetricSpace α] {a b : α}, |dist a
 b| = dist a b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用引理 `Affine.Simplex.abs_inner_vsub_altitudeFoot_lt_mul`：abs_inner_vsub_altitu
deFoot_lt_mul {i j : Fin (n + 1)} (hij : i != j) : |⟪s.points i -ᵥ s.altitudeFoo
t i, s.points j -ᵥ s.altitudeFoot j⟫| <…
-/
lemma abs_inner_vsub_altitudeFoot_div_lt_one {i j : Fin (n + 1)} (hij : i ≠ j) :
    |⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫
            / (s.height i * s.height j)| < 1 := by
  rw [abs_div, div_lt_one (by simp [height])]
  nth_rw 2 [abs_eq_self.2]
  · exact abs_inner_vsub_altitudeFoot_lt_mul _ hij
  · simp only [height]
    positivity
/-
**Affine.Simplex.neg_one_lt_inner_vsub_altitudeFoot_div** 是 Mathlib 中的一个引理，位于命名空
间 `Affine.Simplex`。
形式化陈述：neg_one_lt_inner_vsub_altitudeFoot_div (s : Simplex Real P n) (i j : Fin (
n + 1)) : -1 < ⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫ 
/ (s.height i * s.height j)
参数：s : Simplex Real P n；i j : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStric
tMono α] {a b : α} [AddRightStrictMono α],   -a < b ↔ -b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `neg_div'`：neg_div' (a b : R) : -(b / a) = -b / a
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Affine.Simplex.neg_mul_lt_inner_vsub_altitudeFoot`：neg_mul_lt_inner_vsub
_altitudeFoot (i j : Fin (n + 1)) : -(s.height i * s.height j) < ⟪s.points i -ᵥ 
s.altitudeFoot i, s.points j -ᵥ s.altit…
-/
lemma neg_one_lt_inner_vsub_altitudeFoot_div (s : Simplex ℝ P n) (i j : Fin (n + 1)) :
    -1 < ⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫
            / (s.height i * s.height j) := by
  rw [neg_lt, neg_div', div_lt_one (by simp [height]), neg_lt]
  exact neg_mul_lt_inner_vsub_altitudeFoot _ _ _

end Simplex

end Affine

