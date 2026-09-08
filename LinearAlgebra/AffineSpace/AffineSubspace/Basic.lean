/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Affine spaces

This file gives further properties of affine subspaces (over modules)
and the affine span of a set of points.

## Main definitions

* `AffineSubspace.Parallel`, notation `∥`, gives the property of two affine subspaces being
  parallel (one being a translate of the other).

-/

@[expose] public section

noncomputable section

open Affine

open Set
open scoped Pointwise

section

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P]

/-
**vectorSpan_vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (k : Type u_1) {V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] (s : Set 
P) (v : V), vectorSpan k (v +ᵥ s) = vectorSpan k s
参数：k : Type u_1；s : Set P；v : V；v +ᵥ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.vadd_set_vsub_vadd_set`：∀ {G : Type u_1} {P : Type u_2} [inst : AddC
ommGroup G] [inst_1 : AddTorsor G P] (v : G) (s t : Set P),   (v +ᵥ s) -ᵥ (v +ᵥ 
t) = s -ᵥ t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma vectorSpan_vadd (s : Set P) (v : V) : vectorSpan k (v +ᵥ s) = vectorSpan k s := by
  simp [vectorSpan]

end


namespace AffineSubspace

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

variable {k P}


/-- Given a point in an affine subspace, a result of subtracting that point on the right is in the
direction if and only if the other point is in the subspace. -/
/-
**AffineSubspace.vsub_right_mem_direction_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ineSubspace`。
形式化陈述：vsub_right_mem_direction_iff_mem {s : AffineSubspace k P} {p : P} (hp : p 
in s) (p₂ : P) : p₂ -ᵥ p in s.direction ↔ p₂ in s
参数：hp : p in s；p₂ : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.mem_direction_iff_eq_vsub_right`：mem_direction_iff_eq_vsu
b_right {s : AffineSubspace k P} {p : P} (hp : p in s) (v : V) : v in s.directio
n ↔ exists p₂ in s, v = p₂ -ᵥ p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Given a point in an affine subspace, a result of subtracting that point on the r
ight is in the
direction if and only if the other point is in the subspace.
-/
theorem vsub_right_mem_direction_iff_mem {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (p₂ : P) :
    p₂ -ᵥ p ∈ s.direction ↔ p₂ ∈ s := by
  rw [mem_direction_iff_eq_vsub_right hp]
  simp

/-- Given a point in an affine subspace, a result of subtracting that point on the left is in the
direction if and only if the other point is in the subspace. -/
/-
**AffineSubspace.vsub_left_mem_direction_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Affi
neSubspace`。
形式化陈述：vsub_left_mem_direction_iff_mem {s : AffineSubspace k P} {p : P} (hp : p i
n s) (p₂ : P) : p -ᵥ p₂ in s.direction ↔ p₂ in s
参数：hp : p in s；p₂ : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.mem_direction_iff_eq_vsub_left`：mem_direction_iff_eq_vsub
_left {s : AffineSubspace k P} {p : P} (hp : p in s) (v : V) : v in s.direction 
↔ exists p₂ in s, v = p -ᵥ p₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Given a point in an affine subspace, a result of subtracting that point on the l
eft is in the
direction if and only if the other point is in the subspace.
-/
theorem vsub_left_mem_direction_iff_mem {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (p₂ : P) :
    p -ᵥ p₂ ∈ s.direction ↔ p₂ ∈ s := by
  rw [mem_direction_iff_eq_vsub_left hp]
  simp
/-
**AffineSubspace.toAddTorsor** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
形式化陈述：toAddTorsor (s : AffineSubspace k P) [Nonempty s] : AddTorsor s.direction 
s where vadd a b
参数：s : AffineSubspace k P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toAddTorsor (s : AffineSubspace k P) [Nonempty s] : AddTorsor s.direction s where
  vadd a b := ⟨(a : V) +ᵥ (b : P), vadd_mem_of_mem_direction a.2 b.2⟩
  zero_vadd := fun a => by
    ext
    exact zero_vadd _ _
  add_vadd a b c := by
    ext
    apply add_vadd
  vsub a b := ⟨(a : P) -ᵥ (b : P), (vsub_left_mem_direction_iff_mem a.2 _).mpr b.2⟩
  vsub_vadd' a b := by
    ext
    apply AddTorsor.vsub_vadd'
  vadd_vsub' a b := by
    ext
    apply AddTorsor.vadd_vsub'

@[simp, norm_cast]
/-
**AffineSubspace.coe_vsub** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_vsub (s : AffineSubspace k P) [Nonempty s] (a b : s) : ↑(a -ᵥ b) = (a 
: P) -ᵥ (b : P)
参数：s : AffineSubspace k P；a b : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_vsub (s : AffineSubspace k P) [Nonempty s] (a b : s) : ↑(a -ᵥ b) = (a : P) -ᵥ (b : P) :=
  rfl

@[simp, norm_cast]
/-
**AffineSubspace.coe_vadd** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_vadd (s : AffineSubspace k P) [Nonempty s] (a : s.direction) (b : s) :
 ↑(a +ᵥ b) = (a : V) +ᵥ (b : P)
参数：s : AffineSubspace k P；a : s.direction；b : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_vadd (s : AffineSubspace k P) [Nonempty s] (a : s.direction) (b : s) :
    ↑(a +ᵥ b) = (a : V) +ᵥ (b : P) :=
  rfl

/-- Embedding of an affine subspace to the ambient space, as an affine map. -/
/-
**AffineSubspace.subtype** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：{k : Type u_1} →   {V : Type u_2} →     {P : Type u_3} →       [inst : Rin
g k] →         [inst_1 : AddCommGroup V] →           [inst_2 : _root_.Module k V
] →             [inst_3 : AddTorsor V P] → (s : AffineSubspace k P) → [inst_4 : 
Nonempty ↥s] → ↥s →ᵃ[k] P
参数：s : AffineSubspace k P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of an affine subspace to the ambient space, as an affine map.
-/
protected def subtype (s : AffineSubspace k P) [Nonempty s] : s →ᵃ[k] P where
  toFun := (↑)
  linear := s.direction.subtype
  map_vadd' _ _ := rfl

@[simp]
/-
**AffineSubspace.subtype_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：subtype_linear (s : AffineSubspace k P) [Nonempty s] : s.subtype.linear = 
s.direction.subtype
参数：s : AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_linear (s : AffineSubspace k P) [Nonempty s] :
    s.subtype.linear = s.direction.subtype := rfl

@[simp]
/-
**AffineSubspace.subtype_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：subtype_apply {s : AffineSubspace k P} [Nonempty s] (p : s) : s.subtype p 
= p
参数：p : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_apply {s : AffineSubspace k P} [Nonempty s] (p : s) : s.subtype p = p :=
  rfl
/-
**AffineSubspace.subtype_injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：subtype_injective (s : AffineSubspace k P) [Nonempty s] : Function.Injecti
ve s.subtype
参数：s : AffineSubspace k P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem subtype_injective (s : AffineSubspace k P) [Nonempty s] : Function.Injective s.subtype :=
  Subtype.coe_injective

@[simp]
/-
**AffineSubspace.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_subtype (s : AffineSubspace k P) [Nonempty s] : (s.subtype : s -> P) =
 ((↑) : s -> P)
参数：s : AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype (s : AffineSubspace k P) [Nonempty s] : (s.subtype : s → P) = ((↑) : s → P) :=
  rfl

end AffineSubspace

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.lineMap_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.lineMap_mem {k V P : Type*} [Ring k] [AddCommGroup V] [Module k 
V] [AddTorsor V P] {Q : AffineSubspace k P} {p₀ p₁ : P} (c : k) (h₀ : p₀ in Q) (
h₁ : p₁ in Q) : AffineMap.lineMap p₀ p₁ c in Q
参数：c : k；h₀ : p₀ in Q；h₁ : p₁ in Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用引理 `AffineSubspace.smul_vsub_vadd_mem`：smul_vsub_vadd_mem (s : AffineSubspac
e k P) (c : k) {p₁ p₂ p₃ : P} : p₁ in s -> p₂ in s -> p₃ in s -> c • (p₁ -ᵥ p₂ :
 V) +ᵥ p₃ in s
-/
theorem AffineMap.lineMap_mem {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V]
    [AddTorsor V P] {Q : AffineSubspace k P} {p₀ p₁ : P} (c : k) (h₀ : p₀ ∈ Q) (h₁ : p₁ ∈ Q) :
    AffineMap.lineMap p₀ p₁ c ∈ Q := by
  rw [AffineMap.lineMap_apply]
  exact Q.smul_vsub_vadd_mem c h₁ h₀ h₀
/-
**AffineMap.homothety_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.homothety_mem {k V P : Type*} [CommRing k] [AddCommGroup V] [Mod
ule k V] [AddTorsor V P] {s : AffineSubspace k P} {c : P} (hc : c in s) (r : k) 
{p : P} (hp : p in s) : AffineMap.homothety c r p in s
参数：hc : c in s；r : k；hp : p in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.homothety_eq_lineMap`：homothety_eq_lineMap (c : P1) (r : k) (p
 : P1) : homothety c r p = lineMap c p r
· 使用定理 `AffineMap.lineMap_mem`：AffineMap.lineMap_mem {k V P : Type*} [Ring k] [A
ddCommGroup V] [Module k V] [AddTorsor V P] {Q : AffineSubspace k P} {p₀ p₁ : P}
 (c : k) (h…
-/
theorem AffineMap.homothety_mem {k V P : Type*} [CommRing k] [AddCommGroup V] [Module k V]
    [AddTorsor V P] {s : AffineSubspace k P} {c : P} (hc : c ∈ s) (r : k) {p : P} (hp : p ∈ s) :
    AffineMap.homothety c r p ∈ s := by
  rw [AffineMap.homothety_eq_lineMap]
  exact lineMap_mem r hc hp

namespace AffineSubspace

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AffineSpace V P]

variable (k V) {p₁ p₂ : P}

/-- The affine span of a single point, coerced to a set, contains just that point. -/
@[simp]
/-
**AffineSubspace.coe_affineSpan_singleton** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：coe_affineSpan_singleton (p : P) : (affineSpan k ({p} : Set P) : Set P) = 
{p}
参数：p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.mem_coe`：mem_coe (p : P) (s : AffineSubspace k P) : p in 
(s : Set P) ↔ p in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.vsub_right_mem_direction_iff_mem`：vsub_right_mem_directio
n_iff_mem {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P) : p₂ -ᵥ p in s
.direction ↔ p₂ in s
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vectorSpan_singleton`：vectorSpan_singleton (p : P) : vectorSpan k ({p} :
 Set P) = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The affine span of a single point, coerced to a set, contains just that point.
-/
theorem coe_affineSpan_singleton (p : P) : (affineSpan k ({p} : Set P) : Set P) = {p} := by
  ext x
  rw [mem_coe, ← vsub_right_mem_direction_iff_mem (mem_affineSpan k (Set.mem_singleton p)) _,
    direction_affineSpan]
  simp

/-- A point is in the affine span of a single point if and only if they are equal. -/
@[simp]
/-
**AffineSubspace.mem_affineSpan_singleton** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：mem_affineSpan_singleton : p₁ in affineSpan k ({p₂} : Set P) ↔ p₁ = p₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.coe_affineSpan_singleton`：coe_affineSpan_singleton (p : P
) : (affineSpan k ({p} : Set P) : Set P) = {p}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A point is in the affine span of a single point if and only if they are equal.
-/
theorem mem_affineSpan_singleton : p₁ ∈ affineSpan k ({p₂} : Set P) ↔ p₁ = p₂ := by
  simp [← mem_coe]
/-
**AffineSubspace.unique_affineSpan_singleton** 是 Mathlib 中的一个实例，位于命名空间 `AffineSu
bspace`。
形式化陈述：unique_affineSpan_singleton (p : P) : Unique (affineSpan k {p}) where defa
ult
参数：p : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance unique_affineSpan_singleton (p : P) : Unique (affineSpan k {p}) where
  default := ⟨p, mem_affineSpan _ (Set.mem_singleton _)⟩
  uniq := fun x ↦ Subtype.ext ((mem_affineSpan_singleton _ _).1 x.property)

@[simp]
/-
**AffineSubspace.preimage_coe_affineSpan_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Af
fineSubspace`。
形式化陈述：preimage_coe_affineSpan_singleton (x : P) : ((↑) : affineSpan k ({x} : Set
 P) -> P) ⁻¹' {x} = univ
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.mem_affineSpan_singleton`：mem_affineSpan_singleton : p₁ i
n affineSpan k ({p₂} : Set P) ↔ p₁ = p₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem preimage_coe_affineSpan_singleton (x : P) :
    ((↑) : affineSpan k ({x} : Set P) → P) ⁻¹' {x} = univ :=
  eq_univ_of_forall fun y => (AffineSubspace.mem_affineSpan_singleton _ _).1 y.2

variable (P)

/-- The top affine subspace is linearly equivalent to the affine space.
This is the affine version of `Submodule.topEquiv`. -/
@[simps! linear apply symm_apply_coe]
/-
**AffineSubspace.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：topEquiv : (⊤ : AffineSubspace k P) ≃ᵃ[k] P where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.instNonemptySubtypeMemTop`：∀ (k : Type u_1) (V : Type u_2
) (P : Type u_3) [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [S : AddTorsor V P],…
· 使用定理 `AffineSubspace.direction_top`：direction_top : (⊤ : AffineSubspace k P).d
irection = ⊤

--- 原说明 ---
The top affine subspace is linearly equivalent to the affine space.
This is the affine version of `Submodule.topEquiv`.
-/
def topEquiv : (⊤ : AffineSubspace k P) ≃ᵃ[k] P where
  toEquiv := Equiv.Set.univ P
  linear := .ofEq _ _ (direction_top _ _ _) ≪≫ₗ Submodule.topEquiv
  map_vadd' _ _ := rfl

variable {k V P}
/-
**AffineSubspace.subsingleton_of_subsingleton_span_eq_top** 是 Mathlib 中的一个定理，位于命
名空间 `AffineSubspace`。
形式化陈述：subsingleton_of_subsingleton_span_eq_top {s : Set P} (h₁ : s.Subsingleton)
 (h₂ : affineSpan k s = ⊤) : Subsingleton P
参数：h₁ : s.Subsingleton；h₂ : affineSpan k s = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.nonempty_of_affineSpan_eq_top`：nonempty_of_affineSpan_eq_
top {s : Set P} (h : affineSpan k s = ⊤) : s.Nonempty
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.subsingleton_of_univ_subsingleton`：subsingleton_of_univ_subsingleton
 (h : (univ : Set α).Subsingleton) : Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subsingleton_iff_singleton`：subsingleton_iff_singleton {x} (hx : x i
n s) : s.Subsingleton ↔ s = {x}
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `AffineSubspace.top_coe`：top_coe : ((⊤ : AffineSubspace k P) : Set P) = S
et.univ
· 使用定理 `AffineSubspace.coe_affineSpan_singleton`：coe_affineSpan_singleton (p : P
) : (affineSpan k ({p} : Set P) : Set P) = {p}
· 使用定理 `AffineSubspace.ext_iff`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [
inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 
: AddTorsor …
-/
theorem subsingleton_of_subsingleton_span_eq_top {s : Set P} (h₁ : s.Subsingleton)
    (h₂ : affineSpan k s = ⊤) : Subsingleton P := by
  obtain ⟨p, hp⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top k V P h₂
  have : s = {p} := Subset.antisymm (fun q hq => h₁ hq hp) (by simp [hp])
  rw [this, AffineSubspace.ext_iff, AffineSubspace.coe_affineSpan_singleton,
    AffineSubspace.top_coe, eq_comm, ← subsingleton_iff_singleton (mem_univ _)] at h₂
  exact subsingleton_of_univ_subsingleton h₂
/-
**AffineSubspace.eq_univ_of_subsingleton_span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `
AffineSubspace`。
形式化陈述：eq_univ_of_subsingleton_span_eq_top {s : Set P} (h₁ : s.Subsingleton) (h₂ 
: affineSpan k s = ⊤) : s = (univ : Set P)
参数：h₁ : s.Subsingleton；h₂ : affineSpan k s = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.nonempty_of_affineSpan_eq_top`：nonempty_of_affineSpan_eq_
top {s : Set P} (h : affineSpan k s = ⊤) : s.Nonempty
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subsingleton_iff_singleton`：subsingleton_iff_singleton {x} (hx : x i
n s) : s.Subsingleton ↔ s = {x}
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.subsingleton_univ_iff`：subsingleton_univ_iff : (univ : Set α).Subsin
gleton ↔ Subsingleton α
· 使用定理 `AffineSubspace.subsingleton_of_subsingleton_span_eq_top`：subsingleton_of
_subsingleton_span_eq_top {s : Set P} (h₁ : s.Subsingleton) (h₂ : affineSpan k s
 = ⊤) : Subsingleton P
-/
theorem eq_univ_of_subsingleton_span_eq_top {s : Set P} (h₁ : s.Subsingleton)
    (h₂ : affineSpan k s = ⊤) : s = (univ : Set P) := by
  obtain ⟨p, hp⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top k V P h₂
  have : s = {p} := Subset.antisymm (fun q hq => h₁ hq hp) (by simp [hp])
  rw [this, eq_comm, ← subsingleton_iff_singleton (mem_univ p), subsingleton_univ_iff]
  exact subsingleton_of_subsingleton_span_eq_top h₁ h₂

/-- If one nonempty affine subspace is less than another, the same applies to their directions -/
/-
**AffineSubspace.direction_lt_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：direction_lt_of_nonempty {s₁ s₂ : AffineSubspace k P} (h : s₁ < s₂) (hn : 
(s₁ : Set P).Nonempty) : s₁.direction < s₂.direction
参数：h : s₁ < s₂；hn : (s₁ : Set P).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.lt_iff_le_and_exists`：lt_iff_le_and_exists (s₁ s₂ : Affin
eSubspace k P) : s₁ < s₂ ↔ s₁ <= s₂ ∧ exists p in s₂, p ∉ s₁
· 使用定理 `SetLike.lt_iff_le_and_exists`：lt_iff_le_and_exists : p < q ↔ p <= q ∧ ex
ists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `AffineSubspace.direction_le`：direction_le {s₁ s₂ : AffineSubspace k P} (
h : s₁ <= s₂) : s₁.direction <= s₂.direction
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `AffineSubspace.vsub_right_mem_direction_iff_mem`：vsub_right_mem_directio
n_iff_mem {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P) : p₂ -ᵥ p in s
.direction ↔ p₂ in s

--- 原说明 ---
If one nonempty affine subspace is less than another, the same applies to their 
directions
-/
theorem direction_lt_of_nonempty {s₁ s₂ : AffineSubspace k P} (h : s₁ < s₂)
    (hn : (s₁ : Set P).Nonempty) : s₁.direction < s₂.direction := by
  obtain ⟨p, hp⟩ := hn
  rw [lt_iff_le_and_exists] at h
  rcases h with ⟨hle, p₂, hp₂, hp₂s₁⟩
  rw [SetLike.lt_iff_le_and_exists]
  use direction_le hle, p₂ -ᵥ p, vsub_mem_direction hp₂ (hle hp)
  intro hm
  rw [vsub_right_mem_direction_iff_mem hp p₂] at hm
  exact hp₂s₁ hm

end AffineSubspace

section AffineSpace'

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

variable {ι : Type*}

open AffineSubspace Set

/-- The `vectorSpan` is the span of the pairwise subtractions with a given point on the left. -/
/-
**vectorSpan_eq_span_vsub_set_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_eq_span_vsub_set_left {s : Set P} {p : P} (hp : p in s) : vecto
rSpan k s = Submodule.span k ((p -ᵥ ·) '' s)
参数：hp : p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_def`：vectorSpan_def (s : Set P) : vectorSpan k s = Submodule.
span k (s -ᵥ s)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.mem_span`：mem_span : x in span R s ↔ forall p : Submodule R M,
 s subseteq p -> x in p
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…

--- 原说明 ---
The `vectorSpan` is the span of the pairwise subtractions with a given point on 
the left.
-/
theorem vectorSpan_eq_span_vsub_set_left {s : Set P} {p : P} (hp : p ∈ s) :
    vectorSpan k s = Submodule.span k ((p -ᵥ ·) '' s) := by
  rw [vectorSpan_def]
  refine le_antisymm ?_ (Submodule.span_mono ?_)
  · rw [Submodule.span_le]
    rintro v ⟨p₁, hp₁, p₂, hp₂, hv⟩
    simp_rw [← vsub_sub_vsub_cancel_left p₁ p₂ p] at hv
    rw [← hv, SetLike.mem_coe, Submodule.mem_span]
    exact fun m hm => Submodule.sub_mem _ (hm ⟨p₂, hp₂, rfl⟩) (hm ⟨p₁, hp₁, rfl⟩)
  · rintro v ⟨p₂, hp₂, hv⟩
    exact ⟨p, hp, p₂, hp₂, hv⟩

/-- The `vectorSpan` is the span of the pairwise subtractions with a given point on the right. -/
/-
**vectorSpan_eq_span_vsub_set_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_eq_span_vsub_set_right {s : Set P} {p : P} (hp : p in s) : vect
orSpan k s = Submodule.span k ((· -ᵥ p) '' s)
参数：hp : p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_def`：vectorSpan_def (s : Set P) : vectorSpan k s = Submodule.
span k (s -ᵥ s)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.mem_span`：mem_span : x in span R s ↔ forall p : Submodule R M,
 s subseteq p -> x in p
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…

--- 原说明 ---
The `vectorSpan` is the span of the pairwise subtractions with a given point on 
the right.
-/
theorem vectorSpan_eq_span_vsub_set_right {s : Set P} {p : P} (hp : p ∈ s) :
    vectorSpan k s = Submodule.span k ((· -ᵥ p) '' s) := by
  rw [vectorSpan_def]
  refine le_antisymm ?_ (Submodule.span_mono ?_)
  · rw [Submodule.span_le]
    rintro v ⟨p₁, hp₁, p₂, hp₂, hv⟩
    simp_rw [← vsub_sub_vsub_cancel_right p₁ p₂ p] at hv
    rw [← hv, SetLike.mem_coe, Submodule.mem_span]
    exact fun m hm => Submodule.sub_mem _ (hm ⟨p₁, hp₁, rfl⟩) (hm ⟨p₂, hp₂, rfl⟩)
  · rintro v ⟨p₂, hp₂, hv⟩
    exact ⟨p₂, hp₂, p, hp, hv⟩

/-- The `vectorSpan` is the span of the pairwise subtractions with a given point on the left,
excluding the subtraction of that point from itself. -/
/-
**vectorSpan_eq_span_vsub_set_left_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_eq_span_vsub_set_left_ne {s : Set P} {p : P} (hp : p in s) : ve
ctorSpan k s = Submodule.span k ((p -ᵥ ·) '' (s \ {p}))
参数：hp : p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_eq_span_vsub_set_left`：vectorSpan_eq_span_vsub_set_left {s : 
Set P} {p : P} (hp : p in s) : vectorSpan k s = Submodule.span k ((p -ᵥ ·) '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `Submodule.span_insert_eq_span`：span_insert_eq_span (h : x in span R s) :
 span R (insert x s) = span R s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `vectorSpan` is the span of the pairwise subtractions with a given point on 
the left,
excluding the subtraction of that point from itself.
-/
theorem vectorSpan_eq_span_vsub_set_left_ne {s : Set P} {p : P} (hp : p ∈ s) :
    vectorSpan k s = Submodule.span k ((p -ᵥ ·) '' (s \ {p})) := by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_left k hp, ← Set.insert_eq_of_mem hp, ←
      Set.insert_sdiff_singleton, Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

/-- The `vectorSpan` is the span of the pairwise subtractions with a given point on the right,
excluding the subtraction of that point from itself. -/
/-
**vectorSpan_eq_span_vsub_set_right_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_eq_span_vsub_set_right_ne {s : Set P} {p : P} (hp : p in s) : v
ectorSpan k s = Submodule.span k ((· -ᵥ p) '' (s \ {p}))
参数：hp : p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_eq_span_vsub_set_right`：vectorSpan_eq_span_vsub_set_right {s 
: Set P} {p : P} (hp : p in s) : vectorSpan k s = Submodule.span k ((· -ᵥ p) '' 
s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `Submodule.span_insert_eq_span`：span_insert_eq_span (h : x in span R s) :
 span R (insert x s) = span R s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `vectorSpan` is the span of the pairwise subtractions with a given point on 
the right,
excluding the subtraction of that point from itself.
-/
theorem vectorSpan_eq_span_vsub_set_right_ne {s : Set P} {p : P} (hp : p ∈ s) :
    vectorSpan k s = Submodule.span k ((· -ᵥ p) '' (s \ {p})) := by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_right k hp, ← Set.insert_eq_of_mem hp, ←
      Set.insert_sdiff_singleton, Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

/-- The `vectorSpan` is the span of the pairwise subtractions with a given point on the right,
excluding the subtraction of that point from itself. -/
/-
**vectorSpan_eq_span_vsub_finset_right_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_eq_span_vsub_finset_right_ne [DecidableEq P] [DecidableEq V] {s
 : Finset P} {p : P} (hp : p in s) : vectorSpan k (s : Set P) = Submodule.span k
 ((s.erase p).image (· -ᵥ p))
参数：hp : p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_eq_span_vsub_set_right_ne`：vectorSpan_eq_span_vsub_set_right_
ne {s : Set P} {p : P} (hp : p in s) : vectorSpan k s = Submodule.span k ((· -ᵥ 
p) '' (s \ {p}))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `vectorSpan` is the span of the pairwise subtractions with a given point on 
the right,
excluding the subtraction of that point from itself.
-/
theorem vectorSpan_eq_span_vsub_finset_right_ne [DecidableEq P] [DecidableEq V] {s : Finset P}
    {p : P} (hp : p ∈ s) :
    vectorSpan k (s : Set P) = Submodule.span k ((s.erase p).image (· -ᵥ p)) := by
  simp [vectorSpan_eq_span_vsub_set_right_ne _ (Finset.mem_coe.mpr hp)]

/-- The `vectorSpan` of the image of a function is the span of the pairwise subtractions with a
given point on the left, excluding the subtraction of that point from itself. -/
/-
**vectorSpan_image_eq_span_vsub_set_left_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_image_eq_span_vsub_set_left_ne (p : ι -> P) {s : Set ι} {i : ι}
 (hi : i in s) : vectorSpan k (p '' s) = Submodule.span k ((p i -ᵥ ·) '' p '' (s
 \ {i}))
参数：p : ι -> P；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_eq_span_vsub_set_left`：vectorSpan_eq_span_vsub_set_left {s : 
Set P} {p : P} (hp : p in s) : vectorSpan k s = Submodule.span k ((p -ᵥ ·) '' s)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `Submodule.span_insert_eq_span`：span_insert_eq_span (h : x in span R s) :
 span R (insert x s) = span R s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `vectorSpan` of the image of a function is the span of the pairwise subtract
ions with a
given point on the left, excluding the subtraction of that point from itself.
-/
theorem vectorSpan_image_eq_span_vsub_set_left_ne (p : ι → P) {s : Set ι} {i : ι} (hi : i ∈ s) :
    vectorSpan k (p '' s) = Submodule.span k ((p i -ᵥ ·) '' p '' (s \ {i})) := by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_left k (Set.mem_image_of_mem p hi), ← Set.insert_eq_of_mem hi, ←
      Set.insert_sdiff_singleton, Set.image_insert_eq, Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

/-- The `vectorSpan` of the image of a function is the span of the pairwise subtractions with a
given point on the right, excluding the subtraction of that point from itself. -/
/-
**vectorSpan_image_eq_span_vsub_set_right_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_image_eq_span_vsub_set_right_ne (p : ι -> P) {s : Set ι} {i : ι
} (hi : i in s) : vectorSpan k (p '' s) = Submodule.span k ((· -ᵥ p i) '' p '' (
s \ {i}))
参数：p : ι -> P；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_eq_span_vsub_set_right`：vectorSpan_eq_span_vsub_set_right {s 
: Set P} {p : P} (hp : p in s) : vectorSpan k s = Submodule.span k ((· -ᵥ p) '' 
s)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `Submodule.span_insert_eq_span`：span_insert_eq_span (h : x in span R s) :
 span R (insert x s) = span R s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `vectorSpan` of the image of a function is the span of the pairwise subtract
ions with a
given point on the right, excluding the subtraction of that point from itself.
-/
theorem vectorSpan_image_eq_span_vsub_set_right_ne (p : ι → P) {s : Set ι} {i : ι} (hi : i ∈ s) :
    vectorSpan k (p '' s) = Submodule.span k ((· -ᵥ p i) '' p '' (s \ {i})) := by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_image_of_mem p hi), ← Set.insert_eq_of_mem hi,
      ← Set.insert_sdiff_singleton, Set.image_insert_eq, Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

/-- The `vectorSpan` of an indexed family is the span of the pairwise subtractions with a given
point on the left. -/
/-
**vectorSpan_range_eq_span_range_vsub_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_range_eq_span_range_vsub_left (p : ι -> P) (i0 : ι) : vectorSpa
n k (Set.range p) = Submodule.span k (Set.range fun i : ι => p i0 -ᵥ p i)
参数：p : ι -> P；i0 : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_eq_span_vsub_set_left`：vectorSpan_eq_span_vsub_set_left {s : 
Set P} {p : P} (hp : p in s) : vectorSpan k s = Submodule.span k ((p -ᵥ ·) '' s)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f

--- 原说明 ---
The `vectorSpan` of an indexed family is the span of the pairwise subtractions w
ith a given
point on the left.
-/
theorem vectorSpan_range_eq_span_range_vsub_left (p : ι → P) (i0 : ι) :
    vectorSpan k (Set.range p) = Submodule.span k (Set.range fun i : ι => p i0 -ᵥ p i) := by
  rw [vectorSpan_eq_span_vsub_set_left k (Set.mem_range_self i0), ← Set.range_comp]
  congr

/-- The `vectorSpan` of an indexed family is the span of the pairwise subtractions with a given
point on the right. -/
/-
**vectorSpan_range_eq_span_range_vsub_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_range_eq_span_range_vsub_right (p : ι -> P) (i0 : ι) : vectorSp
an k (Set.range p) = Submodule.span k (Set.range fun i : ι => p i -ᵥ p i0)
参数：p : ι -> P；i0 : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_eq_span_vsub_set_right`：vectorSpan_eq_span_vsub_set_right {s 
: Set P} {p : P} (hp : p in s) : vectorSpan k s = Submodule.span k ((· -ᵥ p) '' 
s)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f

--- 原说明 ---
The `vectorSpan` of an indexed family is the span of the pairwise subtractions w
ith a given
point on the right.
-/
theorem vectorSpan_range_eq_span_range_vsub_right (p : ι → P) (i0 : ι) :
    vectorSpan k (Set.range p) = Submodule.span k (Set.range fun i : ι => p i -ᵥ p i0) := by
  rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_range_self i0), ← Set.range_comp]
  congr

/-- The `vectorSpan` of an indexed family is the span of the pairwise subtractions with a given
point on the left, excluding the subtraction of that point from itself. -/
/-
**vectorSpan_range_eq_span_range_vsub_left_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_range_eq_span_range_vsub_left_ne (p : ι -> P) (i₀ : ι) : vector
Span k (Set.range p) = Submodule.span k (Set.range fun i : { x // x != i₀ } => p
 i₀ -ᵥ p i)
参数：p : ι -> P；i₀ : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `vectorSpan_image_eq_span_vsub_set_left_ne`：vectorSpan_image_eq_span_vsub
_set_left_ne (p : ι -> P) {s : Set ι} {i : ι} (hi : i in s) : vectorSpan k (p ''
 s) = Submodule.span k ((p i -ᵥ…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)

--- 原说明 ---
The `vectorSpan` of an indexed family is the span of the pairwise subtractions w
ith a given
point on the left, excluding the subtraction of that point from itself.
-/
theorem vectorSpan_range_eq_span_range_vsub_left_ne (p : ι → P) (i₀ : ι) :
    vectorSpan k (Set.range p) =
      Submodule.span k (Set.range fun i : { x // x ≠ i₀ } => p i₀ -ᵥ p i) := by
  rw [← Set.image_univ, vectorSpan_image_eq_span_vsub_set_left_ne k _ (Set.mem_univ i₀)]
  congr with v
  simp only [Set.mem_range, Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, Subtype.exists]
  constructor
  · rintro ⟨x, ⟨i₁, ⟨⟨_, hi₁⟩, rfl⟩⟩, hv⟩
    exact ⟨i₁, hi₁, hv⟩
  · exact fun ⟨i₁, hi₁, hv⟩ => ⟨p i₁, ⟨i₁, ⟨Set.mem_univ _, hi₁⟩, rfl⟩, hv⟩

/-- The `vectorSpan` of an indexed family is the span of the pairwise subtractions with a given
point on the right, excluding the subtraction of that point from itself. -/
/-
**vectorSpan_range_eq_span_range_vsub_right_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_range_eq_span_range_vsub_right_ne (p : ι -> P) (i₀ : ι) : vecto
rSpan k (Set.range p) = Submodule.span k (Set.range fun i : { x // x != i₀ } => 
p i -ᵥ p i₀)
参数：p : ι -> P；i₀ : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `vectorSpan_image_eq_span_vsub_set_right_ne`：vectorSpan_image_eq_span_vsu
b_set_right_ne (p : ι -> P) {s : Set ι} {i : ι} (hi : i in s) : vectorSpan k (p 
'' s) = Submodule.span k ((· -ᵥ …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)

--- 原说明 ---
The `vectorSpan` of an indexed family is the span of the pairwise subtractions w
ith a given
point on the right, excluding the subtraction of that point from itself.
-/
theorem vectorSpan_range_eq_span_range_vsub_right_ne (p : ι → P) (i₀ : ι) :
    vectorSpan k (Set.range p) =
      Submodule.span k (Set.range fun i : { x // x ≠ i₀ } => p i -ᵥ p i₀) := by
  rw [← Set.image_univ, vectorSpan_image_eq_span_vsub_set_right_ne k _ (Set.mem_univ i₀)]
  congr with v
  simp only [Set.mem_range, Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, Subtype.exists]
  constructor
  · rintro ⟨x, ⟨i₁, ⟨⟨_, hi₁⟩, rfl⟩⟩, hv⟩
    exact ⟨i₁, hi₁, hv⟩
  · exact fun ⟨i₁, hi₁, hv⟩ => ⟨p i₁, ⟨i₁, ⟨Set.mem_univ _, hi₁⟩, rfl⟩, hv⟩

variable {k}

/-- A set, considered as a subset of its spanned affine subspace, spans the whole subspace. -/
@[simp]
/-
**affineSpan_coe_preimage_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_coe_preimage_eq_top (A : Set P) [Nonempty A] : affineSpan k (((
↑) : affineSpan k A -> P) ⁻¹' A) = ⊤
参数：A : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `affineSpan_induction'`：affineSpan_induction' {s : Set P} {p : forall x, 
x in affineSpan k s -> Prop} (mem : forall (y) (hys : y in s), p y (subset_affin
eSpan k _ h…
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s
· 使用引理 `AffineSubspace.smul_vsub_vadd_mem`：smul_vsub_vadd_mem (s : AffineSubspac
e k P) (c : k) {p₁ p₂ p₃ : P} : p₁ in s -> p₂ in s -> p₃ in s -> c • (p₁ -ᵥ p₂ :
 V) +ᵥ p₃ in s

--- 原说明 ---
A set, considered as a subset of its spanned affine subspace, spans the whole su
bspace.
-/
theorem affineSpan_coe_preimage_eq_top (A : Set P) [Nonempty A] :
    affineSpan k (((↑) : affineSpan k A → P) ⁻¹' A) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  refine affineSpan_induction' (fun y hy ↦ ?_) (fun c u hu v hv w hw ↦ ?_) hx
  · exact subset_affineSpan _ _ hy
  · exact AffineSubspace.smul_vsub_vadd_mem _ _

/-- Suppose a set of vectors spans `V`.  Then a point `p`, together with those vectors added to `p`,
spans `P`. -/
/-
**affineSpan_singleton_union_vadd_eq_top_of_span_eq_top** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：affineSpan_singleton_union_vadd_eq_top_of_span_eq_top {s : Set V} (p : P) 
(h : Submodule.span k (Set.range ((↑) : s -> V)) = ⊤) : affineSpan k ({p} union 
(fun v => v +ᵥ p) '' s) = ⊤
参数：p : P；h : Submodule.span k (Set.range ((↑) : s -> V)) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext_of_direction_eq`：ext_of_direction_eq {s₁ s₂ : AffineS
ubspace k P} (hd : s₁.direction = s₂.direction) (hn : ((s₁ : Set P) inter s₂).No
nempty) : s₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `AffineSubspace.direction_top`：direction_top : (⊤ : AffineSubspace k P).d
irection = ⊤
· 使用定理 `vectorSpan_eq_span_vsub_set_right`：vectorSpan_eq_span_vsub_set_right {s 
: Set P} {p : P} (hp : p in s) : vectorSpan k s = Submodule.span k ((· -ᵥ p) '' 
s)
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `AffineSubspace.mem_top`：mem_top (p : P) : p in (⊤ : AffineSubspace k P)

--- 原说明 ---
Suppose a set of vectors spans `V`.  Then a point `p`, together with those vecto
rs added to `p`,
spans `P`.
-/
theorem affineSpan_singleton_union_vadd_eq_top_of_span_eq_top {s : Set V} (p : P)
    (h : Submodule.span k (Set.range ((↑) : s → V)) = ⊤) :
    affineSpan k ({p} ∪ (fun v => v +ᵥ p) '' s) = ⊤ := by
  convert!
    ext_of_direction_eq _
      ⟨p, mem_affineSpan k (Set.mem_union_left _ (Set.mem_singleton _)), mem_top k V p⟩
  rw [direction_affineSpan, direction_top,
    vectorSpan_eq_span_vsub_set_right k (Set.mem_union_left _ (Set.mem_singleton _) : p ∈ _),
    eq_top_iff, ← h]
  apply Submodule.span_mono
  rintro v ⟨v', rfl⟩
  use (v' : V) +ᵥ p
  simp

variable (k)

/-- The `vectorSpan` of two points is the span of their difference. -/
/-
**vectorSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_pair (p₁ p₂ : P) : vectorSpan k ({p₁, p₂} : Set P) = k ∙ (p₁ -ᵥ
 p₂)
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_eq_span_vsub_set_left`：vectorSpan_eq_span_vsub_set_left {s : 
Set P} {p : P} (hp : p in s) : vectorSpan k s = Submodule.span k ((p -ᵥ ·) '' s)
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.image_pair`：image_pair (f : α -> β) (a b : α) : f '' {a, b} = {f a, 
f b}
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.span_insert_zero`：span_insert_zero : span R (insert (0 : M) s)
 = span R s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `vectorSpan` of two points is the span of their difference.
-/
theorem vectorSpan_pair (p₁ p₂ : P) : vectorSpan k ({p₁, p₂} : Set P) = k ∙ (p₁ -ᵥ p₂) := by
  simp_rw [vectorSpan_eq_span_vsub_set_left k (mem_insert p₁ _), image_pair, vsub_self,
    Submodule.span_insert_zero]

/-- The `vectorSpan` of two points is the span of their difference (reversed). -/
/-
**vectorSpan_pair_rev** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_pair_rev (p₁ p₂ : P) : vectorSpan k ({p₁, p₂} : Set P) = k ∙ (p
₂ -ᵥ p₁)
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用定理 `vectorSpan_pair`：vectorSpan_pair (p₁ p₂ : P) : vectorSpan k ({p₁, p₂} : 
Set P) = k ∙ (p₁ -ᵥ p₂)

--- 原说明 ---
The `vectorSpan` of two points is the span of their difference (reversed).
-/
theorem vectorSpan_pair_rev (p₁ p₂ : P) : vectorSpan k ({p₁, p₂} : Set P) = k ∙ (p₂ -ᵥ p₁) := by
  rw [pair_comm, vectorSpan_pair]

variable {k}

/-- A vector lies in the `vectorSpan` of two points if and only if it is a multiple of their
difference. -/
/-
**mem_vectorSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_vectorSpan_pair {p₁ p₂ : P} {v : V} : v in vectorSpan k ({p₁, p₂} : Se
t P) ↔ exists r : k, r • (p₁ -ᵥ p₂) = v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_pair`：vectorSpan_pair (p₁ p₂ : P) : vectorSpan k ({p₁, p₂} : 
Set P) = k ∙ (p₁ -ᵥ p₂)
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A vector lies in the `vectorSpan` of two points if and only if it is a multiple 
of their
difference.
-/
theorem mem_vectorSpan_pair {p₁ p₂ : P} {v : V} :
    v ∈ vectorSpan k ({p₁, p₂} : Set P) ↔ ∃ r : k, r • (p₁ -ᵥ p₂) = v := by
  rw [vectorSpan_pair, Submodule.mem_span_singleton]

/-- A vector lies in the `vectorSpan` of two points if and only if it is a multiple of their
difference (reversed). -/
/-
**mem_vectorSpan_pair_rev** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_vectorSpan_pair_rev {p₁ p₂ : P} {v : V} : v in vectorSpan k ({p₁, p₂} 
: Set P) ↔ exists r : k, r • (p₂ -ᵥ p₁) = v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_pair_rev`：vectorSpan_pair_rev (p₁ p₂ : P) : vectorSpan k ({p₁
, p₂} : Set P) = k ∙ (p₂ -ᵥ p₁)
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A vector lies in the `vectorSpan` of two points if and only if it is a multiple 
of their
difference (reversed).
-/
theorem mem_vectorSpan_pair_rev {p₁ p₂ : P} {v : V} :
    v ∈ vectorSpan k ({p₁, p₂} : Set P) ↔ ∃ r : k, r • (p₂ -ᵥ p₁) = v := by
  rw [vectorSpan_pair_rev, Submodule.mem_span_singleton]


set_option backward.isDefEq.respectTransparency false in
/-- A combination of two points expressed with `lineMap` lies in their affine span. -/
/-
**AffineMap.lineMap_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.lineMap_mem_affineSpan_pair (r : k) (p₁ p₂ : P) : AffineMap.line
Map p₁ p₂ r in line[k, p₁, p₂]
参数：r : k；p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.lineMap_mem`：AffineMap.lineMap_mem {k V P : Type*} [Ring k] [A
ddCommGroup V] [Module k V] [AddTorsor V P] {Q : AffineSubspace k P} {p₀ p₁ : P}
 (c : k) (h…
· 使用定理 `left_mem_affineSpan_pair`：left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in l
ine[k, p₁, p₂]
· 使用定理 `right_mem_affineSpan_pair`：right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ in
 line[k, p₁, p₂]

--- 原说明 ---
A combination of two points expressed with `lineMap` lies in their affine span.
-/
theorem AffineMap.lineMap_mem_affineSpan_pair (r : k) (p₁ p₂ : P) :
    AffineMap.lineMap p₁ p₂ r ∈ line[k, p₁, p₂] :=
  AffineMap.lineMap_mem _ (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- A combination of two points expressed with `lineMap` (with the two points reversed) lies in
their affine span. -/
/-
**AffineMap.lineMap_rev_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.lineMap_rev_mem_affineSpan_pair (r : k) (p₁ p₂ : P) : AffineMap.
lineMap p₂ p₁ r in line[k, p₁, p₂]
参数：r : k；p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.lineMap_mem`：AffineMap.lineMap_mem {k V P : Type*} [Ring k] [A
ddCommGroup V] [Module k V] [AddTorsor V P] {Q : AffineSubspace k P} {p₀ p₁ : P}
 (c : k) (h…
· 使用定理 `right_mem_affineSpan_pair`：right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ in
 line[k, p₁, p₂]
· 使用定理 `left_mem_affineSpan_pair`：left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in l
ine[k, p₁, p₂]

--- 原说明 ---
A combination of two points expressed with `lineMap` (with the two points revers
ed) lies in
their affine span.
-/
theorem AffineMap.lineMap_rev_mem_affineSpan_pair (r : k) (p₁ p₂ : P) :
    AffineMap.lineMap p₂ p₁ r ∈ line[k, p₁, p₂] :=
  AffineMap.lineMap_mem _ (right_mem_affineSpan_pair _ _ _) (left_mem_affineSpan_pair _ _ _)

/-- A multiple of the difference of two points added to the first point lies in their affine
span. -/
/-
**smul_vsub_vadd_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_vsub_vadd_mem_affineSpan_pair (r : k) (p₁ p₂ : P) : r • (p₂ -ᵥ p₁) +ᵥ
 p₁ in line[k, p₁, p₂]
参数：r : k；p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.lineMap_mem_affineSpan_pair`：AffineMap.lineMap_mem_affineSpan_
pair (r : k) (p₁ p₂ : P) : AffineMap.lineMap p₁ p₂ r in line[k, p₁, p₂]

--- 原说明 ---
A multiple of the difference of two points added to the first point lies in thei
r affine
span.
-/
theorem smul_vsub_vadd_mem_affineSpan_pair (r : k) (p₁ p₂ : P) :
    r • (p₂ -ᵥ p₁) +ᵥ p₁ ∈ line[k, p₁, p₂] :=
  AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- A multiple of the difference of two points added to the second point lies in their affine
span. -/
/-
**smul_vsub_rev_vadd_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_vsub_rev_vadd_mem_affineSpan_pair (r : k) (p₁ p₂ : P) : r • (p₁ -ᵥ p₂
) +ᵥ p₂ in line[k, p₁, p₂]
参数：r : k；p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.lineMap_rev_mem_affineSpan_pair`：AffineMap.lineMap_rev_mem_aff
ineSpan_pair (r : k) (p₁ p₂ : P) : AffineMap.lineMap p₂ p₁ r in line[k, p₁, p₂]

--- 原说明 ---
A multiple of the difference of two points added to the second point lies in the
ir affine
span.
-/
theorem smul_vsub_rev_vadd_mem_affineSpan_pair (r : k) (p₁ p₂ : P) :
    r • (p₁ -ᵥ p₂) +ᵥ p₂ ∈ line[k, p₁, p₂] :=
  AffineMap.lineMap_rev_mem_affineSpan_pair _ _ _

/-- A vector added to the first point lies in the affine span of two points if and only if it is
a multiple of their difference. -/
/-
**vadd_left_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vadd_left_mem_affineSpan_pair {p₁ p₂ : P} {v : V} : v +ᵥ p₁ in line[k, p₁,
 p₂] ↔ exists r : k, r • (p₂ -ᵥ p₁) = v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.vadd_mem_iff_mem_direction`：vadd_mem_iff_mem_direction {s
 : AffineSubspace k P} (v : V) {p : P} (hp : p in s) : v +ᵥ p in s ↔ v in s.dire
ction
· 使用定理 `left_mem_affineSpan_pair`：left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in l
ine[k, p₁, p₂]
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `mem_vectorSpan_pair_rev`：mem_vectorSpan_pair_rev {p₁ p₂ : P} {v : V} : v
 in vectorSpan k ({p₁, p₂} : Set P) ↔ exists r : k, r • (p₂ -ᵥ p₁) = v
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A vector added to the first point lies in the affine span of two points if and o
nly if it is
a multiple of their difference.
-/
theorem vadd_left_mem_affineSpan_pair {p₁ p₂ : P} {v : V} :
    v +ᵥ p₁ ∈ line[k, p₁, p₂] ↔ ∃ r : k, r • (p₂ -ᵥ p₁) = v := by
  rw [vadd_mem_iff_mem_direction _ (left_mem_affineSpan_pair _ _ _), direction_affineSpan,
    mem_vectorSpan_pair_rev]

/-- A vector added to the second point lies in the affine span of two points if and only if it is
a multiple of their difference. -/
/-
**vadd_right_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vadd_right_mem_affineSpan_pair {p₁ p₂ : P} {v : V} : v +ᵥ p₂ in line[k, p₁
, p₂] ↔ exists r : k, r • (p₁ -ᵥ p₂) = v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.vadd_mem_iff_mem_direction`：vadd_mem_iff_mem_direction {s
 : AffineSubspace k P} (v : V) {p : P} (hp : p in s) : v +ᵥ p in s ↔ v in s.dire
ction
· 使用定理 `right_mem_affineSpan_pair`：right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ in
 line[k, p₁, p₂]
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `mem_vectorSpan_pair`：mem_vectorSpan_pair {p₁ p₂ : P} {v : V} : v in vect
orSpan k ({p₁, p₂} : Set P) ↔ exists r : k, r • (p₁ -ᵥ p₂) = v
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A vector added to the second point lies in the affine span of two points if and 
only if it is
a multiple of their difference.
-/
theorem vadd_right_mem_affineSpan_pair {p₁ p₂ : P} {v : V} :
    v +ᵥ p₂ ∈ line[k, p₁, p₂] ↔ ∃ r : k, r • (p₁ -ᵥ p₂) = v := by
  rw [vadd_mem_iff_mem_direction _ (right_mem_affineSpan_pair _ _ _), direction_affineSpan,
    mem_vectorSpan_pair]

set_option backward.isDefEq.respectTransparency false in
/-
**mem_affineSpan_pair_iff_exists_lineMap_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_affineSpan_pair_iff_exists_lineMap_eq {p p₁ p₂ : P} : p in line[k, p₁,
 p₂] ↔ exists r : k, AffineMap.lineMap p₁ p₂ r = p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_left_mem_affineSpan_pair`：vadd_left_mem_affineSpan_pair {p₁ p₂ : P}
 {v : V} : v +ᵥ p₁ in line[k, p₁, p₂] ↔ exists r : k, r • (p₂ -ᵥ p₁) = v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `AffineMap.lineMap_mem_affineSpan_pair`：AffineMap.lineMap_mem_affineSpan_
pair (r : k) (p₁ p₂ : P) : AffineMap.lineMap p₁ p₂ r in line[k, p₁, p₂]
-/
lemma mem_affineSpan_pair_iff_exists_lineMap_eq {p p₁ p₂ : P} :
    p ∈ line[k, p₁, p₂] ↔ ∃ r : k, AffineMap.lineMap p₁ p₂ r = p := by
  constructor
  · intro h
    rw [← vsub_vadd p p₁, vadd_left_mem_affineSpan_pair] at h
    obtain ⟨r, hr⟩ := h
    refine ⟨r, ?_⟩
    rw [← vsub_vadd p p₁, ← hr, AffineMap.lineMap_apply]
  · rintro ⟨r, rfl⟩
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**mem_affineSpan_pair_iff_exists_lineMap_rev_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_affineSpan_pair_iff_exists_lineMap_rev_eq {p p₁ p₂ : P} : p in line[k,
 p₁, p₂] ↔ exists r : k, AffineMap.lineMap p₂ p₁ r = p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用引理 `mem_affineSpan_pair_iff_exists_lineMap_eq`：mem_affineSpan_pair_iff_exist
s_lineMap_eq {p p₁ p₂ : P} : p in line[k, p₁, p₂] ↔ exists r : k, AffineMap.line
Map p₁ p₂ r = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_affineSpan_pair_iff_exists_lineMap_rev_eq {p p₁ p₂ : P} :
    p ∈ line[k, p₁, p₂] ↔ ∃ r : k, AffineMap.lineMap p₂ p₁ r = p := by
  rw [Set.pair_comm, mem_affineSpan_pair_iff_exists_lineMap_eq]

end AffineSpace'

namespace AffineSubspace

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

/-- The direction of the sup of two nonempty affine subspaces is the sup of the two directions and
of any one difference between points in the two subspaces. -/
/-
**AffineSubspace.direction_sup** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：direction_sup {s₁ s₂ : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ in s₁) (h
p₂ : p₂ in s₂) : (s₁ ⊔ s₂).direction = s₁.direction ⊔ s₂.direction ⊔ k ∙ (p₂ -ᵥ 
p₁)
参数：hp₁ : p₁ in s₁；hp₂ : p₂ in s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `vectorSpan_eq_span_vsub_set_right`：vectorSpan_eq_span_vsub_set_right {s 
: Set P} {p : P} (hp : p in s) : vectorSpan k s = Submodule.span k ((· -ᵥ p) '' 
s)
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.mem_coe`：mem_coe (p : P) (s : AffineSubspace k P) : p in 
(s : Set P) ↔ p in s
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `AffineSubspace.sup_direction_le`：sup_direction_le (s₁ s₂ : AffineSubspac
e k P) : s₁.direction ⊔ s₂.direction <= (s₁ ⊔ s₂).direction
· 使用定理 `AffineSubspace.direction_eq_vectorSpan`：direction_eq_vectorSpan (s : Aff
ineSubspace k P) : s.direction = vectorSpan k (s : Set P)
· 使用定理 `vectorSpan_def`：vectorSpan_def (s : Set P) : vectorSpan k s = Submodule.
span k (s -ᵥ s)
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.vsub_mem_vsub`：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] {s 
t : Set β} {b c : β}, b ∈ s → c ∈ t → b -ᵥ c ∈ s -ᵥ t
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_union_right`：mem_union_right {x : α} {b : Set α} (a : Set α) : x
 in b -> x in a union b

--- 原说明 ---
The direction of the sup of two nonempty affine subspaces is the sup of the two 
directions and
of any one difference between points in the two subspaces.
-/
theorem direction_sup {s₁ s₂ : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s₁) (hp₂ : p₂ ∈ s₂) :
    (s₁ ⊔ s₂).direction = s₁.direction ⊔ s₂.direction ⊔ k ∙ (p₂ -ᵥ p₁) := by
  refine le_antisymm ?_ ?_
  · change (affineSpan k ((s₁ : Set P) ∪ s₂)).direction ≤ _
    rw [← mem_coe] at hp₁
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right k (Set.mem_union_left _ hp₁),
      Submodule.span_le]
    rintro v ⟨p₃, hp₃, rfl⟩
    rcases hp₃ with hp₃ | hp₃
    · rw [sup_assoc, sup_comm, SetLike.mem_coe, Submodule.mem_sup]
      use 0, Submodule.zero_mem _, p₃ -ᵥ p₁, vsub_mem_direction hp₃ hp₁
      rw [zero_add]
    · rw [sup_assoc, SetLike.mem_coe, Submodule.mem_sup]
      use 0, Submodule.zero_mem _, p₃ -ᵥ p₁
      rw [and_comm, zero_add]
      use rfl
      rw [← vsub_add_vsub_cancel p₃ p₂ p₁, Submodule.mem_sup]
      use p₃ -ᵥ p₂, vsub_mem_direction hp₃ hp₂, p₂ -ᵥ p₁, Submodule.mem_span_singleton_self _
  · refine sup_le (sup_direction_le _ _) ?_
    rw [direction_eq_vectorSpan, vectorSpan_def]
    exact
      sInf_le_sInf fun p hp =>
        Set.Subset.trans
          (Set.singleton_subset_iff.2
            (vsub_mem_vsub (mem_affineSpan k (Set.mem_union_right _ hp₂))
              (mem_affineSpan k (Set.mem_union_left _ hp₁))))
          hp

/-- The direction of the sup of two affine subspaces with a common point is the sup of the two
directions. -/
/-
**AffineSubspace.direction_sup_eq_sup_direction** 是 Mathlib 中的一个引理，位于命名空间 `Affin
eSubspace`。
形式化陈述：direction_sup_eq_sup_direction {s₁ s₂ : AffineSubspace k P} {p : P} (hp₁ :
 p in s₁) (hp₂ : p in s₂) : (s₁ ⊔ s₂).direction = s₁.direction ⊔ s₂.direction
参数：hp₁ : p in s₁；hp₂ : p in s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.direction_sup`：direction_sup {s₁ s₂ : AffineSubspace k P}
 {p₁ p₂ : P} (hp₁ : p₁ in s₁) (hp₂ : p₂ in s₂) : (s₁ ⊔ s₂).direction = s₁.direct
ion ⊔ s₂.direction…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The direction of the sup of two affine subspaces with a common point is the sup 
of the two
directions.
-/
lemma direction_sup_eq_sup_direction {s₁ s₂ : AffineSubspace k P} {p : P} (hp₁ : p ∈ s₁)
    (hp₂ : p ∈ s₂) : (s₁ ⊔ s₂).direction = s₁.direction ⊔ s₂.direction := by
  rw [direction_sup hp₁ hp₂]
  simp

/-- The direction of the span of the result of adding a point to a nonempty affine subspace is the
sup of the direction of that subspace and of any one difference between that point and a point in
the subspace. -/
/-
**AffineSubspace.direction_affineSpan_insert** 是 Mathlib 中的一个定理，位于命名空间 `AffineSu
bspace`。
形式化陈述：direction_affineSpan_insert {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁
 in s) : (affineSpan k (insert p₂ (s : Set P))).direction = Submodule.span k {p₂
 -ᵥ p₁} ⊔ s.direction
参数：hp₁ : p₁ in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `AffineSubspace.coe_affineSpan_singleton`：coe_affineSpan_singleton (p : P
) : (affineSpan k ({p} : Set P) : Set P) = {p}
· 使用定理 `AffineSubspace.direction_sup`：direction_sup {s₁ s₂ : AffineSubspace k P}
 {p₁ p₂ : P} (hp₁ : p₁ in s₁) (hp₂ : p₂ in s₂) : (s₁ ⊔ s₂).direction = s₁.direct
ion ⊔ s₂.direction…
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vectorSpan_singleton`：vectorSpan_singleton (p : P) : vectorSpan k ({p} :
 Set P) = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The direction of the span of the result of adding a point to a nonempty affine s
ubspace is the
sup of the direction of that subspace and of any one difference between that poi
nt and a point in
the subspace.
-/
theorem direction_affineSpan_insert {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s) :
    (affineSpan k (insert p₂ (s : Set P))).direction =
    Submodule.span k {p₂ -ᵥ p₁} ⊔ s.direction := by
  rw [sup_comm, ← Set.union_singleton, ← coe_affineSpan_singleton k V p₂]
  change (s ⊔ affineSpan k {p₂}).direction = _
  rw [direction_sup hp₁ (mem_affineSpan k (Set.mem_singleton _)), direction_affineSpan]
  simp

/-- Given a point `p₁` in an affine subspace `s`, and a point `p₂`, a point `p` is in the span of
`s` with `p₂` added if and only if it is a multiple of `p₂ -ᵥ p₁` added to a point in `s`. -/
/-
**AffineSubspace.mem_affineSpan_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
形式化陈述：mem_affineSpan_insert_iff {s : AffineSubspace k P} {p₁ : P} (hp₁ : p₁ in s
) (p₂ p : P) : p in affineSpan k (insert p₂ (s : Set P)) ↔ exists r : k, exists 
p0 in s, p = r • (p₂ -ᵥ p₁ : V) +ᵥ p0
参数：hp₁ : p₁ in s；p₂ p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.vsub_right_mem_direction_iff_mem`：vsub_right_mem_directio
n_iff_mem {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P) : p₂ -ᵥ p in s
.direction ↔ p₂ in s
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `AffineSubspace.mem_coe`：mem_coe (p : P) (s : AffineSubspace k P) : p in 
(s : Set P) ↔ p in s
· 使用定理 `AffineSubspace.direction_affineSpan_insert`：direction_affineSpan_insert 
{s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ in s) : (affineSpan k (insert p₂ 
(s : Set P))).direction = Submod…
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `vadd_vadd`：∀ {M : Type u_1} {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (a₁ a₂ : M) (b : α),   a₁ +ᵥ a₂ +ᵥ b = (a₁ + a₂) +ᵥ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)

--- 原说明 ---
Given a point `p₁` in an affine subspace `s`, and a point `p₂`, a point `p` is i
n the span of
`s` with `p₂` added if and only if it is a multiple of `p₂ -ᵥ p₁` added to a poi
nt in `s`.
-/
theorem mem_affineSpan_insert_iff {s : AffineSubspace k P} {p₁ : P} (hp₁ : p₁ ∈ s) (p₂ p : P) :
    p ∈ affineSpan k (insert p₂ (s : Set P)) ↔
      ∃ r : k, ∃ p0 ∈ s, p = r • (p₂ -ᵥ p₁ : V) +ᵥ p0 := by
  rw [← mem_coe] at hp₁
  rw [← vsub_right_mem_direction_iff_mem (mem_affineSpan k (Set.mem_insert_of_mem _ hp₁)),
    direction_affineSpan_insert hp₁, Submodule.mem_sup]
  constructor
  · rintro ⟨v₁, hv₁, v₂, hv₂, hp⟩
    rw [Submodule.mem_span_singleton] at hv₁
    rcases hv₁ with ⟨r, rfl⟩
    use r, v₂ +ᵥ p₁, vadd_mem_of_mem_direction hv₂ hp₁
    symm at hp
    rw [← sub_eq_zero, ← vsub_vadd_eq_vsub_sub, vsub_eq_zero_iff_eq] at hp
    rw [hp, vadd_vadd]
  · rintro ⟨r, p₃, hp₃, rfl⟩
    use r • (p₂ -ᵥ p₁), Submodule.mem_span_singleton.2 ⟨r, rfl⟩, p₃ -ᵥ p₁,
      vsub_mem_direction hp₃ hp₁
    rw [vadd_vsub_assoc]

variable (k) in
/-- The vector span of a union of sets with a common point is the sup of their vector spans. -/
/-
**AffineSubspace.vectorSpan_union_of_mem_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Affin
eSubspace`。
形式化陈述：vectorSpan_union_of_mem_of_mem {s₁ s₂ : Set P} {p : P} (hp₁ : p in s₁) (hp
₂ : p in s₂) : vectorSpan k (s₁ union s₂) = vectorSpan k s₁ ⊔ vectorSpan k s₂
参数：hp₁ : p in s₁；hp₂ : p in s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineSubspace.span_union`：span_union (s t : Set P) : affineSpan k (s un
ion t) = affineSpan k s ⊔ affineSpan k t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `AffineSubspace.direction_sup_eq_sup_direction`：direction_sup_eq_sup_dire
ction {s₁ s₂ : AffineSubspace k P} {p : P} (hp₁ : p in s₁) (hp₂ : p in s₂) : (s₁
 ⊔ s₂).direction = s₁.direction ⊔ s…
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The vector span of a union of sets with a common point is the sup of their vecto
r spans.
-/
lemma vectorSpan_union_of_mem_of_mem {s₁ s₂ : Set P} {p : P} (hp₁ : p ∈ s₁) (hp₂ : p ∈ s₂) :
    vectorSpan k (s₁ ∪ s₂) = vectorSpan k s₁ ⊔ vectorSpan k s₂ := by
  simp_rw [← direction_affineSpan, span_union,
    direction_sup_eq_sup_direction (mem_affineSpan k hp₁) (mem_affineSpan k hp₂)]

end AffineSubspace

section MapComap

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]
variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]
variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

section

variable (f : P₁ →ᵃ[k] P₂)

/-- The affine version of `LinearMap.map_span`. -/
@[simp]
/-
**AffineMap.map_vectorSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.map_vectorSpan {s : Set P₁} : Submodule.map f.linear (vectorSpan
 k s) = vectorSpan k (f '' s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.image_vsub_image`：image_vsub_image {s t : Set P1} (f : P1 ->ᵃ[
k] P2) : f '' s -ᵥ f '' t = f.linear '' (s -ᵥ t)
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The affine version of `LinearMap.map_span`.
-/
theorem AffineMap.map_vectorSpan {s : Set P₁} :
    Submodule.map f.linear (vectorSpan k s) = vectorSpan k (f '' s) := by
  simp [vectorSpan_def, f.image_vsub_image]

-- this name was backwards
@[deprecated (since := "2026-01-20")]
alias AffineMap.vectorSpan_image_eq_submodule_map := AffineMap.map_vectorSpan

namespace AffineSubspace

/-- The image of an affine subspace under an affine map as an affine subspace. -/
/-
**AffineSubspace.map** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：map (s : AffineSubspace k P₁) : AffineSubspace k P₂ where carrier
参数：s : AffineSubspace k P₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of an affine subspace under an affine map as an affine subspace.
-/
def map (s : AffineSubspace k P₁) : AffineSubspace k P₂ where
  carrier := f '' s
  smul_vsub_vadd_mem' := by
    rintro t - - - ⟨p₁, h₁, rfl⟩ ⟨p₂, h₂, rfl⟩ ⟨p₃, h₃, rfl⟩
    use t • (p₁ -ᵥ p₂) +ᵥ p₃
    suffices t • (p₁ -ᵥ p₂) +ᵥ p₃ ∈ s by
    { simp only [SetLike.mem_coe, true_and, this]
      rw [AffineMap.map_vadd, map_smul, AffineMap.linearMap_vsub] }
    exact s.smul_vsub_vadd_mem t h₁ h₂ h₃

@[simp]
/-
**AffineSubspace.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_map (s : AffineSubspace k P₁) : (s.map f : Set P₂) = f '' s
参数：s : AffineSubspace k P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (s : AffineSubspace k P₁) : (s.map f : Set P₂) = f '' s :=
  rfl

@[simp]
/-
**AffineSubspace.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：mem_map {f : P₁ ->ᵃ[k] P₂} {x : P₂} {s : AffineSubspace k P₁} : x in s.map
 f ↔ exists y in s, f y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map {f : P₁ →ᵃ[k] P₂} {x : P₂} {s : AffineSubspace k P₁} :
    x ∈ s.map f ↔ ∃ y ∈ s, f y = x :=
  Iff.rfl
/-
**AffineSubspace.mem_map_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：mem_map_of_mem {x : P₁} {s : AffineSubspace k P₁} (h : x in s) : f x in s.
map f
参数：h : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem mem_map_of_mem {x : P₁} {s : AffineSubspace k P₁} (h : x ∈ s) : f x ∈ s.map f :=
  Set.mem_image_of_mem _ h

@[simp 1100]
/-
**AffineSubspace.mem_map_iff_mem_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineS
ubspace`。
形式化陈述：mem_map_iff_mem_of_injective {f : P₁ ->ᵃ[k] P₂} {x : P₁} {s : AffineSubspa
ce k P₁} (hf : Function.Injective f) : f x in s.map f ↔ x in s
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
-/
theorem mem_map_iff_mem_of_injective {f : P₁ →ᵃ[k] P₂} {x : P₁} {s : AffineSubspace k P₁}
    (hf : Function.Injective f) : f x ∈ s.map f ↔ x ∈ s :=
  hf.mem_set_image

@[simp]
/-
**AffineSubspace.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：map_bot : (⊥ : AffineSubspace k P₁).map f = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.coe_injective`：coe_injective : Function.Injective ((↑) : 
AffineSubspace k P -> Set P)
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
-/
theorem map_bot : (⊥ : AffineSubspace k P₁).map f = ⊥ :=
  coe_injective <| image_empty f

@[simp]
/-
**AffineSubspace.map_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：map_eq_bot_iff {s : AffineSubspace k P₁} : s.map f = ⊥ ↔ s = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.coe_eq_bot_iff`：coe_eq_bot_iff (Q : AffineSubspace k P) :
 (Q : Set P) = ∅ ↔ Q = ⊥
· 使用定理 `Set.image_eq_empty`：image_eq_empty {α β} {f : α -> β} {s : Set α} : f ''
 s = ∅ ↔ s = ∅
· 使用定理 `AffineSubspace.coe_map`：coe_map (s : AffineSubspace k P₁) : (s.map f : S
et P₂) = f '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.map_bot`：map_bot : (⊥ : AffineSubspace k P₁).map f = ⊥
-/
theorem map_eq_bot_iff {s : AffineSubspace k P₁} : s.map f = ⊥ ↔ s = ⊥ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rwa [← coe_eq_bot_iff, coe_map, image_eq_empty, coe_eq_bot_iff] at h
  · rw [h, map_bot]

@[simp]
/-
**AffineSubspace.map_id** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：map_id (s : AffineSubspace k P₁) : s.map (AffineMap.id k P₁) = s
参数：s : AffineSubspace k P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.coe_injective`：coe_injective : Function.Injective ((↑) : 
AffineSubspace k P -> Set P)
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem map_id (s : AffineSubspace k P₁) : s.map (AffineMap.id k P₁) = s :=
  coe_injective <| image_id _
/-
**AffineSubspace.map_map** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：map_map (s : AffineSubspace k P₁) (f : P₁ ->ᵃ[k] P₂) (g : P₂ ->ᵃ[k] P₃) : 
(s.map f).map g = s.map (g.comp f)
参数：s : AffineSubspace k P₁；f : P₁ ->ᵃ[k] P₂；g : P₂ ->ᵃ[k] P₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.coe_injective`：coe_injective : Function.Injective ((↑) : 
AffineSubspace k P -> Set P)
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map (s : AffineSubspace k P₁) (f : P₁ →ᵃ[k] P₂) (g : P₂ →ᵃ[k] P₃) :
    (s.map f).map g = s.map (g.comp f) :=
  coe_injective <| image_image _ _ _

@[simp]
/-
**AffineSubspace.map_direction** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：map_direction (s : AffineSubspace k P₁) : (s.map f).direction = s.directio
n.map f.linear
参数：s : AffineSubspace k P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.map_vectorSpan`：AffineMap.map_vectorSpan {s : Set P₁} : Submod
ule.map f.linear (vectorSpan k s) = vectorSpan k (f '' s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_direction (s : AffineSubspace k P₁) :
    (s.map f).direction = s.direction.map f.linear := by
  simp [direction_eq_vectorSpan, AffineMap.map_vectorSpan]
/-
**AffineSubspace.map_span** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：map_span (s : Set P₁) : (affineSpan k s).map f = affineSpan k (f '' s)
参数：s : Set P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.span_empty`：span_empty : affineSpan k (∅ : Set P) = ⊥
· 使用定理 `AffineSubspace.map_bot`：map_bot : (⊥ : AffineSubspace k P₁).map f = ⊥
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.ext_of_direction_eq`：ext_of_direction_eq {s₁ s₂ : AffineS
ubspace k P} (hd : s₁.direction = s₂.direction) (hn : ((s₁ : Set P) inter s₂).No
nempty) : s₁ = s₂
· 使用定理 `AffineSubspace.map_direction`：map_direction (s : AffineSubspace k P₁) : 
(s.map f).direction = s.direction.map f.linear
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `AffineMap.map_vectorSpan`：AffineMap.map_vectorSpan {s : Set P₁} : Submod
ule.map f.linear (vectorSpan k s) = vectorSpan k (f '' s)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s
-/
theorem map_span (s : Set P₁) : (affineSpan k s).map f = affineSpan k (f '' s) := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · simp
  apply ext_of_direction_eq
  · simp [direction_affineSpan]
  · exact ⟨f p, mem_image_of_mem f (subset_affineSpan k _ hp),
          subset_affineSpan k _ (mem_image_of_mem f hp)⟩

@[gcongr]
/-
**AffineSubspace.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：map_mono {s₁ s₂ : AffineSubspace k P₁} (h : s₁ <= s₂) : s₁.map f <= s₂.map
 f
参数：h : s₁ <= s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem map_mono {s₁ s₂ : AffineSubspace k P₁} (h : s₁ ≤ s₂) : s₁.map f ≤ s₂.map f :=
  Set.image_mono h
/-
**AffineSubspace.map_inf_le** 是 Mathlib 中的一个引理，位于命名空间 `AffineSubspace`。
形式化陈述：map_inf_le (s₁ s₂ : AffineSubspace k P₁) : (s₁ ⊓ s₂).map f <= s₁.map f ⊓ s
₂.map f
参数：s₁ s₂ : AffineSubspace k P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `AffineSubspace.map_mono`：map_mono {s₁ s₂ : AffineSubspace k P₁} (h : s₁ 
<= s₂) : s₁.map f <= s₂.map f
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
lemma map_inf_le (s₁ s₂ : AffineSubspace k P₁) : (s₁ ⊓ s₂).map f ≤ s₁.map f ⊓ s₂.map f :=
  le_inf (map_mono _ inf_le_left) (map_mono _ inf_le_right)
/-
**AffineSubspace.map_inf_eq** 是 Mathlib 中的一个引理，位于命名空间 `AffineSubspace`。
形式化陈述：map_inf_eq (hf : Function.Injective f) (s₁ s₂ : AffineSubspace k P₁) : (s₁
 ⊓ s₂).map f = s₁.map f ⊓ s₂.map f
参数：hf : Function.Injective f；s₁ s₂ : AffineSubspace k P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma map_inf_eq (hf : Function.Injective f) (s₁ s₂ : AffineSubspace k P₁) :
    (s₁ ⊓ s₂).map f = s₁.map f ⊓ s₂.map f := by
  ext p
  simp [mem_inf_iff]
  grind
/-
**AffineSubspace.map_mk'** 是 Mathlib 中的一个引理，位于命名空间 `AffineSubspace`。
形式化陈述：map_mk' (p : P₁) (direction : Submodule k V₁) : (mk' p direction).map f = 
mk' (f p) (direction.map f.linear)
参数：p : P₁；direction : Submodule k V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
-/
lemma map_mk' (p : P₁) (direction : Submodule k V₁) :
    (mk' p direction).map f = mk' (f p) (direction.map f.linear) := by
  ext q
  simp only [mem_map, mem_mk', Submodule.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r -ᵥ p, hr, by simp⟩
  · rintro ⟨r, hr, he⟩
    exact ⟨r +ᵥ p, by simp [hr], by simp [he]⟩

section inclusion
variable {S₁ S₂ : AffineSubspace k P₁} [Nonempty S₁]

/-- Affine map from a smaller to a larger subspace of the same space.

This is the affine version of `Submodule.inclusion`. -/
@[simps linear]
/-
**AffineSubspace.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：inclusion (h : S₁ <= S₂) : letI
参数：h : S₁ <= S₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.direction_le`：direction_le {s₁ s₂ : AffineSubspace k P} (
h : s₁ <= s₂) : s₁.direction <= s₂.direction

--- 原说明 ---
Affine map from a smaller to a larger subspace of the same space.

This is the affine version of `Submodule.inclusion`.
-/
def inclusion (h : S₁ ≤ S₂) :
    letI := Nonempty.map (Set.inclusion h) ‹_›
    S₁ →ᵃ[k] S₂ :=
  letI := Nonempty.map (Set.inclusion h) ‹_›
  { toFun := Set.inclusion h
    linear := Submodule.inclusion <| AffineSubspace.direction_le h
    map_vadd' := fun ⟨_,_⟩ ⟨_,_⟩ => rfl }

@[simp]
/-
**AffineSubspace.coe_inclusion_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_inclusion_apply (h : S₁ <= S₂) (x : S₁) : (inclusion h x : P₁) = x
参数：h : S₁ <= S₂；x : S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem coe_inclusion_apply (h : S₁ ≤ S₂) (x : S₁) : (inclusion h x : P₁) = x :=
  rfl

@[simp]
/-
**AffineSubspace.inclusion_rfl** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：inclusion_rfl : inclusion (le_refl S₁) = AffineMap.id k S₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem inclusion_rfl : inclusion (le_refl S₁) = AffineMap.id k S₁ := rfl

end inclusion

end AffineSubspace

namespace AffineMap

@[simp]
/-
**AffineMap.map_top_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：map_top_of_surjective (hf : Function.Surjective f) : AffineSubspace.map f 
⊤ = ⊤
参数：hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.ext_iff`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [
inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 
: AddTorsor …
· 使用定理 `Set.image_univ_of_surjective`：image_univ_of_surjective {ι : Type*} {f : 
ι -> β} (H : Surjective f) : f '' univ = univ
-/
theorem map_top_of_surjective (hf : Function.Surjective f) : AffineSubspace.map f ⊤ = ⊤ := by
  rw [AffineSubspace.ext_iff]
  exact image_univ_of_surjective hf
/-
**AffineMap.span_eq_top_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：span_eq_top_of_surjective {s : Set P₁} (hf : Function.Surjective f) (h : a
ffineSpan k s = ⊤) : affineSpan k (f '' s) = ⊤
参数：hf : Function.Surjective f；h : affineSpan k s = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
· 使用定理 `AffineMap.map_top_of_surjective`：map_top_of_surjective (hf : Function.Su
rjective f) : AffineSubspace.map f ⊤ = ⊤
-/
theorem span_eq_top_of_surjective {s : Set P₁} (hf : Function.Surjective f)
    (h : affineSpan k s = ⊤) : affineSpan k (f '' s) = ⊤ := by
  rw [← AffineSubspace.map_span, h, map_top_of_surjective f hf]

/-- If two affine maps agree on a set, their linear parts agree on the vector span of that set. -/
/-
**AffineMap.linear_eqOn_vectorSpan** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：linear_eqOn_vectorSpan {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [Ad
dTorsor V₂ P₂] {s : Set P₁} {f g : P₁ ->ᵃ[k] P₂} (h_agree : s.EqOn f g) : Set.Eq
On f.linear g.linear (vectorSpan k s)
参数：h_agree : s.EqOn f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.eqOn_span`：eqOn_span {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (H : S
et.EqOn f g s) ⦃x⦄ (h : x in span R s) : f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If two affine maps agree on a set, their linear parts agree on the vector span o
f that set.
-/
theorem linear_eqOn_vectorSpan {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {s : Set P₁} {f g : P₁ →ᵃ[k] P₂}
    (h_agree : s.EqOn f g) : Set.EqOn f.linear g.linear (vectorSpan k s) := by
  simp only [vectorSpan_def]
  apply LinearMap.eqOn_span
  rintro - ⟨x, hx, y, hy, rfl⟩
  simp [h_agree hx, h_agree hy]

/-- Two affine maps which agree on a set, agree on its affine span. -/
/-
**AffineMap.eqOn_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：eqOn_affineSpan {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor
 V₂ P₂] {s : Set P₁} {f g : P₁ ->ᵃ[k] P₂} (h_agree : s.EqOn f g) : Set.EqOn f g 
(affineSpan k s)
参数：h_agree : s.EqOn f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.span_empty`：span_empty : affineSpan k (∅ : Set P) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `AffineMap.linear_eqOn_vectorSpan`：linear_eqOn_vectorSpan {V₂ P₂ : Type*}
 [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] {s : Set P₁} {f g : P₁ ->ᵃ[k]
 P₂} (h_agree : s.EqOn…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two affine maps which agree on a set, agree on its affine span.
-/
theorem eqOn_affineSpan {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {s : Set P₁} {f g : P₁ →ᵃ[k] P₂}
    (h_agree : s.EqOn f g) : Set.EqOn f g (affineSpan k s) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨q, hq⟩; · simp
  rintro - ⟨x, hx, y, hy, rfl⟩
  simp [h_agree hx, linear_eqOn_vectorSpan h_agree hy]

/-- If two affine maps agree on a set that spans the entire space, then they are equal. -/
/-
**AffineMap.ext_on** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：ext_on {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] {
s : Set P₁} {f g : P₁ ->ᵃ[k] P₂} (h_span : affineSpan k s = ⊤) (h_agree : s.EqOn
 f g) : f = g
参数：h_span : affineSpan k s = ⊤；h_agree : s.EqOn f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.eqOn_affineSpan`：eqOn_affineSpan {V₂ P₂ : Type*} [AddCommGroup
 V₂] [Module k V₂] [AddTorsor V₂ P₂] {s : Set P₁} {f g : P₁ ->ᵃ[k] P₂} (h_agree 
: s.EqOn f g) :…

--- 原说明 ---
If two affine maps agree on a set that spans the entire space, then they are equ
al.
-/
theorem ext_on {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {s : Set P₁} {f g : P₁ →ᵃ[k] P₂}
    (h_span : affineSpan k s = ⊤)
    (h_agree : s.EqOn f g) : f = g := by
  simpa [h_span] using eqOn_affineSpan h_agree

end AffineMap

namespace AffineEquiv

/-- If two affine equivalences agree on a set that spans the entire space, then they are equal. -/
/-
**AffineEquiv.ext_on** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：ext_on {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] {
s : Set P₁} (h_span : affineSpan k s = ⊤) (T₁ T₂ : P₁ ≃ᵃ[k] P₂) (h_agree : s.EqO
n T₁ T₂) : T₁ = T₂
参数：h_span : affineSpan k s = ⊤；T₁ T₂ : P₁ ≃ᵃ[k] P₂；h_agree : s.EqOn T₁ T₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineEquiv.toAffineMap_inj`：toAffineMap_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.to
AffineMap = e'.toAffineMap ↔ e = e'
· 使用定理 `AffineMap.ext_on`：ext_on {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂]
 [AddTorsor V₂ P₂] {s : Set P₁} {f g : P₁ ->ᵃ[k] P₂} (h_span : affineSpan k s = 
⊤) (h_…

--- 原说明 ---
If two affine equivalences agree on a set that spans the entire space, then they
 are equal.
-/
theorem ext_on {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {s : Set P₁} (h_span : affineSpan k s = ⊤)
    (T₁ T₂ : P₁ ≃ᵃ[k] P₂) (h_agree : s.EqOn T₁ T₂) : T₁ = T₂ :=
  AffineEquiv.toAffineMap_inj.mp <| AffineMap.ext_on h_span h_agree

section ofEq
variable (S₁ S₂ : AffineSubspace k P₁) [Nonempty S₁] [Nonempty S₂]

/-- Affine equivalence between two equal affine subspace.

This is the affine version of `LinearEquiv.ofEq`. -/
@[simps linear]
/-
**AffineEquiv.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：ofEq (h : S₁ = S₂) : S₁ ≃ᵃ[k] S₂ where toEquiv
参数：h : S₁ = S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Affine equivalence between two equal affine subspace.

This is the affine version of `LinearEquiv.ofEq`.
-/
def ofEq (h : S₁ = S₂) : S₁ ≃ᵃ[k] S₂ where
  toEquiv := Equiv.setCongr <| congr_arg _ h
  linear := .ofEq _ _ <| congr_arg _ h
  map_vadd' := fun ⟨_,_⟩ ⟨_,_⟩ => rfl

@[simp]
/-
**AffineEquiv.coe_ofEq_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_ofEq_apply (h : S₁ = S₂) (x : S₁) : (ofEq S₁ S₂ h x : P₁) = x
参数：h : S₁ = S₂；x : S₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofEq_apply (h : S₁ = S₂) (x : S₁) : (ofEq S₁ S₂ h x : P₁) = x :=
  rfl

@[simp]
/-
**AffineEquiv.ofEq_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：ofEq_symm (h : S₁ = S₂) : (ofEq S₁ S₂ h).symm = ofEq S₂ S₁ h.symm
参数：h : S₁ = S₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.ext`：ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e
 = e'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem ofEq_symm (h : S₁ = S₂) : (ofEq S₁ S₂ h).symm = ofEq S₂ S₁ h.symm := by
  ext
  rfl

@[simp]
/-
**AffineEquiv.ofEq_rfl** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：ofEq_rfl : ofEq S₁ S₁ rfl = AffineEquiv.refl k S₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofEq_rfl : ofEq S₁ S₁ rfl = AffineEquiv.refl k S₁ := rfl

end ofEq

/-
**AffineEquiv.span_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：span_eq_top_iff {s : Set P₁} (e : P₁ ≃ᵃ[k] P₂) : affineSpan k s = ⊤ ↔ affi
neSpan k (e '' s) = ⊤
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.span_eq_top_of_surjective`：span_eq_top_of_surjective {s : Set 
P₁} (hf : Function.Surjective f) (h : affineSpan k s = ⊤) : affineSpan k (f '' s
) = ⊤
· 使用定理 `AffineEquiv.surjective`：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3}
 {V₁ : Type u_6} {V₂ : Type u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [i
nst_2 : AddC…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `AffineEquiv.symm_apply_apply`：symm_apply_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₁
) : e.symm (e p) = p
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem span_eq_top_iff {s : Set P₁} (e : P₁ ≃ᵃ[k] P₂) :
    affineSpan k s = ⊤ ↔ affineSpan k (e '' s) = ⊤ := by
  refine ⟨(e : P₁ →ᵃ[k] P₂).span_eq_top_of_surjective e.surjective, ?_⟩
  intro h
  have : s = e.symm '' e '' s := by rw [← image_comp]; simp
  rw [this]
  exact (e.symm : P₂ →ᵃ[k] P₁).span_eq_top_of_surjective e.symm.surjective h

end AffineEquiv

end

namespace AffineSubspace

/-- The preimage of an affine subspace under an affine map as an affine subspace. -/
/-
**AffineSubspace.comap** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：comap (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₂) : AffineSubspace k P₁ w
here carrier
参数：f : P₁ ->ᵃ[k] P₂；s : AffineSubspace k P₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of an affine subspace under an affine map as an affine subspace.
-/
def comap (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₂) : AffineSubspace k P₁ where
  carrier := f ⁻¹' s
  smul_vsub_vadd_mem' t p₁ p₂ p₃ (hp₁ : f p₁ ∈ s) (hp₂ : f p₂ ∈ s) (hp₃ : f p₃ ∈ s) :=
    show f _ ∈ s by
      rw [AffineMap.map_vadd, map_smul, AffineMap.linearMap_vsub]
      apply s.smul_vsub_vadd_mem _ hp₁ hp₂ hp₃

@[simp]
/-
**AffineSubspace.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_comap (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₂) : (s.comap f : Set 
P₁) = f ⁻¹' ↑s
参数：f : P₁ ->ᵃ[k] P₂；s : AffineSubspace k P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₂) : (s.comap f : Set P₁) = f ⁻¹' ↑s :=
  rfl

@[simp]
/-
**AffineSubspace.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：mem_comap {f : P₁ ->ᵃ[k] P₂} {x : P₁} {s : AffineSubspace k P₂} : x in s.c
omap f ↔ f x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {f : P₁ →ᵃ[k] P₂} {x : P₁} {s : AffineSubspace k P₂} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl

@[gcongr]
/-
**AffineSubspace.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：comap_mono {f : P₁ ->ᵃ[k] P₂} {s t : AffineSubspace k P₂} : s <= t -> s.co
map f <= t.comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem comap_mono {f : P₁ →ᵃ[k] P₂} {s t : AffineSubspace k P₂} : s ≤ t → s.comap f ≤ t.comap f :=
  preimage_mono

@[simp]
/-
**AffineSubspace.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：comap_top {f : P₁ ->ᵃ[k] P₂} : (⊤ : AffineSubspace k P₂).comap f = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.ext_iff`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [
inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 
: AddTorsor …
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
-/
theorem comap_top {f : P₁ →ᵃ[k] P₂} : (⊤ : AffineSubspace k P₂).comap f = ⊤ := by
  rw [AffineSubspace.ext_iff]
  exact preimage_univ (f := f)
/-
**AffineSubspace.comap_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {k : Type u_1} {V₁ : Type u_2} {P₁ : Type u_3} {V₂ : Type u_4} {P₂ : Typ
e u_5} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [inst_2 : _root_.Module k V₁
] [inst_3 : AddTorsor V₁ P₁] [inst_4 : AddCommGroup V₂]   [inst_5 : _root_.Modul
e k V₂] [inst_6 : AddTorsor V₂ P₂] (f : P₁ →ᵃ[k] P₂), AffineSubspace.comap f ⊥ =
 ⊥
参数：f : P₁ →ᵃ[k] P₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem comap_bot (f : P₁ →ᵃ[k] P₂) : comap f ⊥ = ⊥ := rfl

@[simp]
/-
**AffineSubspace.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：comap_id (s : AffineSubspace k P₁) : s.comap (AffineMap.id k P₁) = s
参数：s : AffineSubspace k P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_id (s : AffineSubspace k P₁) : s.comap (AffineMap.id k P₁) = s :=
  rfl
/-
**AffineSubspace.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：comap_comap (s : AffineSubspace k P₃) (f : P₁ ->ᵃ[k] P₂) (g : P₂ ->ᵃ[k] P₃
) : (s.comap g).comap f = s.comap (g.comp f)
参数：s : AffineSubspace k P₃；f : P₁ ->ᵃ[k] P₂；g : P₂ ->ᵃ[k] P₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap (s : AffineSubspace k P₃) (f : P₁ →ᵃ[k] P₂) (g : P₂ →ᵃ[k] P₃) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

-- lemmas about map and comap derived from the Galois connection
/-
**AffineSubspace.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：map_le_iff_le_comap {f : P₁ ->ᵃ[k] P₂} {s : AffineSubspace k P₁} {t : Affi
neSubspace k P₂} : s.map f <= t ↔ s <= t.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap {f : P₁ →ᵃ[k] P₂} {s : AffineSubspace k P₁} {t : AffineSubspace k P₂} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  image_subset_iff
/-
**AffineSubspace.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：gc_map_comap (f : P₁ ->ᵃ[k] P₂) : GaloisConnection (map f) (comap f)
参数：f : P₁ ->ᵃ[k] P₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.map_le_iff_le_comap`：map_le_iff_le_comap {f : P₁ ->ᵃ[k] P
₂} {s : AffineSubspace k P₁} {t : AffineSubspace k P₂} : s.map f <= t ↔ s <= t.c
omap f
-/
theorem gc_map_comap (f : P₁ →ᵃ[k] P₂) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap
/-
**AffineSubspace.map_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：map_comap_le (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₂) : (s.comap f).ma
p f <= s
参数：f : P₁ ->ᵃ[k] P₂；s : AffineSubspace k P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `AffineSubspace.gc_map_comap`：gc_map_comap (f : P₁ ->ᵃ[k] P₂) : GaloisCon
nection (map f) (comap f)
-/
theorem map_comap_le (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₂) : (s.comap f).map f ≤ s :=
  (gc_map_comap f).l_u_le _
/-
**AffineSubspace.le_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：le_comap_map (f : P₁ ->ᵃ[k] P₂) (s : AffineSubspace k P₁) : s <= (s.map f)
.comap f
参数：f : P₁ ->ᵃ[k] P₂；s : AffineSubspace k P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `AffineSubspace.gc_map_comap`：gc_map_comap (f : P₁ ->ᵃ[k] P₂) : GaloisCon
nection (map f) (comap f)
-/
theorem le_comap_map (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₁) : s ≤ (s.map f).comap f :=
  (gc_map_comap f).le_u_l _
/-
**AffineSubspace.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：map_sup (s t : AffineSubspace k P₁) (f : P₁ ->ᵃ[k] P₂) : (s ⊔ t).map f = s
.map f ⊔ t.map f
参数：s t : AffineSubspace k P₁；f : P₁ ->ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `AffineSubspace.gc_map_comap`：gc_map_comap (f : P₁ ->ᵃ[k] P₂) : GaloisCon
nection (map f) (comap f)
-/
theorem map_sup (s t : AffineSubspace k P₁) (f : P₁ →ᵃ[k] P₂) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup
/-
**AffineSubspace.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：map_iSup {ι : Sort*} (f : P₁ ->ᵃ[k] P₂) (s : ι -> AffineSubspace k P₁) : (
iSup s).map f = ⨆ i, (s i).map f
参数：f : P₁ ->ᵃ[k] P₂；s : ι -> AffineSubspace k P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `AffineSubspace.gc_map_comap`：gc_map_comap (f : P₁ ->ᵃ[k] P₂) : GaloisCon
nection (map f) (comap f)
-/
theorem map_iSup {ι : Sort*} (f : P₁ →ᵃ[k] P₂) (s : ι → AffineSubspace k P₁) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup
/-
**AffineSubspace.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：comap_inf (s t : AffineSubspace k P₂) (f : P₁ ->ᵃ[k] P₂) : (s ⊓ t).comap f
 = s.comap f ⊓ t.comap f
参数：s t : AffineSubspace k P₂；f : P₁ ->ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `AffineSubspace.gc_map_comap`：gc_map_comap (f : P₁ ->ᵃ[k] P₂) : GaloisCon
nection (map f) (comap f)
-/
theorem comap_inf (s t : AffineSubspace k P₂) (f : P₁ →ᵃ[k] P₂) :
    (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf
/-
**AffineSubspace.comap_supr** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：comap_supr {ι : Sort*} (f : P₁ ->ᵃ[k] P₂) (s : ι -> AffineSubspace k P₂) :
 (iInf s).comap f = ⨅ i, (s i).comap f
参数：f : P₁ ->ᵃ[k] P₂；s : ι -> AffineSubspace k P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `AffineSubspace.gc_map_comap`：gc_map_comap (f : P₁ ->ᵃ[k] P₂) : GaloisCon
nection (map f) (comap f)
-/
theorem comap_supr {ι : Sort*} (f : P₁ →ᵃ[k] P₂) (s : ι → AffineSubspace k P₂) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
/-
**AffineSubspace.comap_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：comap_symm (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁) : s.comap (e.symm :
 P₂ ->ᵃ[k] P₁) = s.map e
参数：e : P₁ ≃ᵃ[k] P₂；s : AffineSubspace k P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.coe_injective`：coe_injective : Function.Injective ((↑) : 
AffineSubspace k P -> Set P)
· 使用定理 `AffineEquiv.preimage_symm`：preimage_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₁) 
: f.symm ⁻¹' s = f '' s
-/
theorem comap_symm (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁) :
    s.comap (e.symm : P₂ →ᵃ[k] P₁) = s.map e :=
  coe_injective <| e.preimage_symm _

@[simp]
/-
**AffineSubspace.map_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：map_symm (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₂) : s.map (e.symm : P₂ 
->ᵃ[k] P₁) = s.comap e
参数：e : P₁ ≃ᵃ[k] P₂；s : AffineSubspace k P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.coe_injective`：coe_injective : Function.Injective ((↑) : 
AffineSubspace k P -> Set P)
· 使用定理 `AffineEquiv.image_symm`：image_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) : f.sy
mm '' s = f ⁻¹' s
-/
theorem map_symm (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₂) :
    s.map (e.symm : P₂ →ᵃ[k] P₁) = s.comap e :=
  coe_injective <| e.image_symm _
/-
**AffineSubspace.comap_span** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：comap_span (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) : (affineSpan k s).comap (f : P₁
 ->ᵃ[k] P₂) = affineSpan k (f ⁻¹' s)
参数：f : P₁ ≃ᵃ[k] P₂；s : Set P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.map_symm`：map_symm (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace 
k P₂) : s.map (e.symm : P₂ ->ᵃ[k] P₁) = s.comap e
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
· 使用定理 `AffineEquiv.coe_coe`：coe_coe (e : P₁ ≃ᵃ[k] P₂) : ((e : P₁ ->ᵃ[k] P₂) : P
₁ -> P₂) = e
· 使用定理 `AffineEquiv.image_symm`：image_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) : f.sy
mm '' s = f ⁻¹' s
-/
theorem comap_span (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) :
    (affineSpan k s).comap (f : P₁ →ᵃ[k] P₂) = affineSpan k (f ⁻¹' s) := by
  rw [← map_symm, map_span, AffineEquiv.coe_coe, f.image_symm]

/-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/
/-
**AffineSubspace.gciMapComap** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：gciMapComap {f : P₁ ->ᵃ[k] P₂} (hf : Function.Injective f) : GaloisCoinser
tion (map f) (comap f)
参数：hf : Function.Injective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.gc_map_comap`：gc_map_comap (f : P₁ ->ᵃ[k] P₂) : GaloisCon
nection (map f) (comap f)

--- 原说明 ---
`map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective.
-/
def gciMapComap {f : P₁ →ᵃ[k] P₂} (hf : Function.Injective f) :
    GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun s p ↦ by simp; grind
/-
**AffineSubspace.comap_map_eq_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `AffineSubs
pace`。
形式化陈述：comap_map_eq_of_injective {f : P₁ ->ᵃ[k] P₂} (hf : Function.Injective f) (
s : AffineSubspace k P₁) : (s.map f).comap f = s
参数：hf : Function.Injective f；s : AffineSubspace k P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_l_eq`：∀ {α : Type u} {β : Type v} {u : α → β} {l : β
 → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsertion l 
u) (b : β), u …
-/
lemma comap_map_eq_of_injective {f : P₁ →ᵃ[k] P₂} (hf : Function.Injective f)
    (s : AffineSubspace k P₁) : (s.map f).comap f = s :=
  (gciMapComap hf).u_l_eq _

end AffineSubspace

end MapComap

namespace AffineSubspace

open AffineEquiv

variable {k V W P Q : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]
  [AddCommGroup W] [Module k W] [AffineSpace W Q]

/-- The product of two affine subspaces as an affine subspace. -/
/-
**AffineSubspace.prod** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：prod (s : AffineSubspace k P) (t : AffineSubspace k Q) : AffineSubspace k 
(P × Q) where carrier
参数：s : AffineSubspace k P；t : AffineSubspace k Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two affine subspaces as an affine subspace.
-/
def prod (s : AffineSubspace k P) (t : AffineSubspace k Q) : AffineSubspace k (P × Q) where
  carrier := (s : Set P) ×ˢ (t : Set Q)
  smul_vsub_vadd_mem' c _ _ _ hp₁ hp₂ hp₃ :=
    ⟨s.smul_vsub_vadd_mem' c hp₁.1 hp₂.1 hp₃.1, t.smul_vsub_vadd_mem' c hp₁.2 hp₂.2 hp₃.2⟩

@[simp]
/-
**AffineSubspace.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_prod (s : AffineSubspace k P) (t : AffineSubspace k Q) : (s.prod t : S
et (P × Q)) = (s : Set P) ×ˢ (t : Set Q)
参数：s : AffineSubspace k P；t : AffineSubspace k Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (s : AffineSubspace k P) (t : AffineSubspace k Q) :
    (s.prod t : Set (P × Q)) = (s : Set P) ×ˢ (t : Set Q) :=
  rfl

@[simp]
/-
**AffineSubspace.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：mem_prod (s : AffineSubspace k P) (t : AffineSubspace k Q) (x : P × Q) : x
 in s.prod t ↔ x.1 in s ∧ x.2 in t
参数：s : AffineSubspace k P；t : AffineSubspace k Q；x : P × Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_prod`：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
-/
theorem mem_prod (s : AffineSubspace k P) (t : AffineSubspace k Q) (x : P × Q) :
    x ∈ s.prod t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Set.mem_prod

@[gcongr]
/-
**AffineSubspace.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：prod_mono {s₁ s₂ : AffineSubspace k P} {t₁ t₂ : AffineSubspace k Q} (hs : 
s₁ <= s₂) (ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod t₂
参数：hs : s₁ <= s₂；ht : t₁ <= t₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono {s₁ s₂ : AffineSubspace k P} {t₁ t₂ : AffineSubspace k Q}
    (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) : s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht

@[simp]
/-
**AffineSubspace.prod_top_top** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：prod_top_top : (⊤ : AffineSubspace k P).prod (⊤ : AffineSubspace k Q) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_top_top : (⊤ : AffineSubspace k P).prod (⊤ : AffineSubspace k Q) = ⊤ := by
  ext; simp

@[simp]
/-
**AffineSubspace.prod_bot_right** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：prod_bot_right (s : AffineSubspace k P) : s.prod (⊥ : AffineSubspace k Q) 
= ⊥
参数：s : AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_bot_right (s : AffineSubspace k P) : s.prod (⊥ : AffineSubspace k Q) = ⊥ := by
  simp [AffineSubspace.ext_iff]

@[simp]
/-
**AffineSubspace.prod_bot_left** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：prod_bot_left (t : AffineSubspace k P) : (⊥ : AffineSubspace k Q).prod t =
 ⊥
参数：t : AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_prod`：empty_prod : (∅ : Set α) ×ˢ t = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_bot_left (t : AffineSubspace k P) : (⊥ : AffineSubspace k Q).prod t = ⊥ := by
  simp [AffineSubspace.ext_iff]
/-
**AffineSubspace.prod_inf_prod** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：prod_inf_prod (s₁ s₂ : AffineSubspace k P) (t₁ t₂ : AffineSubspace k Q) : 
s₁.prod t₁ ⊓ s₂.prod t₂ = (s₁ ⊓ s₂).prod (t₁ ⊓ t₂)
参数：s₁ s₂ : AffineSubspace k P；t₁ t₂ : AffineSubspace k Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.prod_inter_prod`：prod_inter_prod : s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ int
er s₂) ×ˢ (t₁ inter t₂)
-/
theorem prod_inf_prod (s₁ s₂ : AffineSubspace k P) (t₁ t₂ : AffineSubspace k Q) :
    s₁.prod t₁ ⊓ s₂.prod t₂ = (s₁ ⊓ s₂).prod (t₁ ⊓ t₂) :=
  SetLike.coe_injective Set.prod_inter_prod
/-
**AffineSubspace._root_.vectorSpan_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.vectorSpan_prod_le (s : Set P) (t : Set Q) :
    vectorSpan k (s ×ˢ t) ≤ (vectorSpan k s).prod (vectorSpan k t) := by
  simpa [vectorSpan_def, Set.prod_vsub_prod_comm] using Submodule.span_prod_le (s -ᵥ s) (t -ᵥ t)
/-
**AffineSubspace.direction_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：direction_prod_le (s : AffineSubspace k P) (t : AffineSubspace k Q) : (s.p
rod t).direction <= s.direction.prod t.direction
参数：s : AffineSubspace k P；t : AffineSubspace k Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vectorSpan_prod_le`：∀ {k : Type u_1} {V : Type u_2} {W : Type u_3} {P : 
Type u_4} {Q : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V]   [inst_2 : _
root_.Mo…
-/
theorem direction_prod_le (s : AffineSubspace k P) (t : AffineSubspace k Q) :
    (s.prod t).direction ≤ s.direction.prod t.direction := by
  simpa [direction_eq_vectorSpan, coe_prod] using vectorSpan_prod_le (s : Set P) (t : Set Q)
/-
**AffineSubspace._root_.vectorSpan_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.vectorSpan_prod_eq {s : Set P} {t : Set Q} (hs : s.Nonempty) (ht : t.Nonempty) :
    vectorSpan k (s ×ˢ t) = (vectorSpan k s).prod (vectorSpan k t) := by
  rw [vectorSpan_def, Set.prod_vsub_prod_comm]
  exact Submodule.span_prod_eq k hs.zero_mem_vsub_self ht.zero_mem_vsub_self
/-
**AffineSubspace.direction_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：direction_prod_eq {s : AffineSubspace k P} {t : AffineSubspace k Q} (hs : 
s != ⊥) (ht : t != ⊥) : (s.prod t).direction = s.direction.prod t.direction
参数：hs : s != ⊥；ht : t != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_prod_eq`：∀ {k : Type u_1} {V : Type u_2} {W : Type u_3} {P : 
Type u_4} {Q : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V]   [inst_2 : _
root_.Mo…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem direction_prod_eq {s : AffineSubspace k P} {t : AffineSubspace k Q}
    (hs : s ≠ ⊥) (ht : t ≠ ⊥) :
    (s.prod t).direction = s.direction.prod t.direction := by
  simp [direction_eq_vectorSpan, vectorSpan_prod_eq, nonempty_iff_ne_bot, ht, hs]
/-
**AffineSubspace._root_.affineSpan_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.affineSpan_prod_eq (s : Set P) (t : Set Q) :
    affineSpan k (s ×ˢ t) = (affineSpan k s).prod (affineSpan k t) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
  apply AffineSubspace.ext_of_direction_eq
  · simp [direction_prod_eq, Set.nonempty_iff_ne_empty.mp, hs, ht, direction_affineSpan,
      vectorSpan_prod_eq]
  · obtain ⟨x, hx⟩ := hs
    obtain ⟨y, hy⟩ := ht
    use ⟨x, y⟩
    simp [mem_affineSpan, hx, hy]

/-- Two affine subspaces are parallel if one is related to the other by adding the same vector
to all points. -/
@[wikidata Q53875]
/-
**AffineSubspace.Parallel** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：Parallel (s₁ s₂ : AffineSubspace k P) : Prop
参数：s₁ s₂ : AffineSubspace k P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two affine subspaces are parallel if one is related to the other by adding the s
ame vector
to all points.
-/
def Parallel (s₁ s₂ : AffineSubspace k P) : Prop :=
  ∃ v : V, s₂ = s₁.map (constVAdd k P v)

@[inherit_doc]
scoped[Affine] infixl:50 " ∥ " => AffineSubspace.Parallel

@[symm]
/-
**AffineSubspace.Parallel.symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.Paralle
l`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] {s₁ s₂ : 
AffineSubspace k P}, s₁.Parallel s₂ → s₂.Parallel s₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.map_map`：map_map (s : AffineSubspace k P₁) (f : P₁ ->ᵃ[k]
 P₂) (g : P₂ ->ᵃ[k] P₃) : (s.map f).map g = s.map (g.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineEquiv.coe_trans_to_affineMap`：coe_trans_to_affineMap (e : P₁ ≃ᵃ[k]
 P₂) (e' : P₂ ≃ᵃ[k] P₃) : (e.trans e' : P₁ ->ᵃ[k] P₃) = (e' : P₂ ->ᵃ[k] P₃).comp
 e
· 使用定理 `AffineEquiv.constVAdd_add`：constVAdd_add (v w : V₁) : constVAdd k P₁ (v 
+ w) = (constVAdd k P₁ w).trans (constVAdd k P₁ v)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `AffineEquiv.constVAdd_zero`：constVAdd_zero : constVAdd k P₁ 0 = AffineEq
uiv.refl _ _
· 使用定理 `AffineEquiv.coe_refl_to_affineMap`：coe_refl_to_affineMap : ↑(refl k P₁) 
= AffineMap.id k P₁
· 使用定理 `AffineSubspace.map_id`：map_id (s : AffineSubspace k P₁) : s.map (AffineM
ap.id k P₁) = s
-/
theorem Parallel.symm {s₁ s₂ : AffineSubspace k P} (h : s₁ ∥ s₂) : s₂ ∥ s₁ := by
  rcases h with ⟨v, rfl⟩
  refine ⟨-v, ?_⟩
  rw [map_map, ← coe_trans_to_affineMap, ← constVAdd_add, neg_add_cancel, constVAdd_zero,
    coe_refl_to_affineMap, map_id]
/-
**AffineSubspace.parallel_comm** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：parallel_comm {s₁ s₂ : AffineSubspace k P} : s₁ ∥ s₂ ↔ s₂ ∥ s₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.Parallel.symm`：∀ {k : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [i
nst_3 : AddTorsor …
-/
theorem parallel_comm {s₁ s₂ : AffineSubspace k P} : s₁ ∥ s₂ ↔ s₂ ∥ s₁ :=
  ⟨Parallel.symm, Parallel.symm⟩

@[refl]
/-
**AffineSubspace.Parallel.refl** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.Paralle
l`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] (s : Affi
neSubspace k P), s.Parallel s
参数：s : AffineSubspace k P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineEquiv.constVAdd_zero`：constVAdd_zero : constVAdd k P₁ 0 = AffineEq
uiv.refl _ _
· 使用定理 `AffineSubspace.map_id`：map_id (s : AffineSubspace k P₁) : s.map (AffineM
ap.id k P₁) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Parallel.refl (s : AffineSubspace k P) : s ∥ s :=
  ⟨0, by simp⟩

@[trans]
/-
**AffineSubspace.Parallel.trans** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.Parall
el`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] {s₁ s₂ s₃
 : AffineSubspace k P}, s₁.Parallel s₂ → s₂.Parallel s₃ → s₁.Parallel s₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.map_map`：map_map (s : AffineSubspace k P₁) (f : P₁ ->ᵃ[k]
 P₂) (g : P₂ ->ᵃ[k] P₃) : (s.map f).map g = s.map (g.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineEquiv.coe_trans_to_affineMap`：coe_trans_to_affineMap (e : P₁ ≃ᵃ[k]
 P₂) (e' : P₂ ≃ᵃ[k] P₃) : (e.trans e' : P₁ ->ᵃ[k] P₃) = (e' : P₂ ->ᵃ[k] P₃).comp
 e
· 使用定理 `AffineEquiv.constVAdd_add`：constVAdd_add (v w : V₁) : constVAdd k P₁ (v 
+ w) = (constVAdd k P₁ w).trans (constVAdd k P₁ v)
-/
theorem Parallel.trans {s₁ s₂ s₃ : AffineSubspace k P} (h₁₂ : s₁ ∥ s₂) (h₂₃ : s₂ ∥ s₃) :
    s₁ ∥ s₃ := by
  rcases h₁₂ with ⟨v₁₂, rfl⟩
  rcases h₂₃ with ⟨v₂₃, rfl⟩
  refine ⟨v₂₃ + v₁₂, ?_⟩
  rw [map_map, ← coe_trans_to_affineMap, ← constVAdd_add]
/-
**AffineSubspace.** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Refl (α := AffineSubspace k P) Parallel where
  refl := .refl
/-
**AffineSubspace.** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Symm (α := AffineSubspace k P) Parallel where
  symm _ _ := .symm
/-
**AffineSubspace.** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTrans (AffineSubspace k P) Parallel where
  trans _ _ _ := .trans
/-
**AffineSubspace.Parallel.equivalence** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.
Parallel`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P], Equivale
nce AffineSubspace.Parallel
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.Parallel.refl`：∀ {k : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [i
nst_3 : AddTorsor …
· 使用定理 `AffineSubspace.Parallel.symm`：∀ {k : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [i
nst_3 : AddTorsor …
· 使用定理 `AffineSubspace.Parallel.trans`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
inst_3 : AddTorsor …
-/
theorem Parallel.equivalence : Equivalence (α := AffineSubspace k P) Parallel :=
  ⟨.refl, .symm, .trans⟩
/-
**AffineSubspace.Parallel.direction_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
.Parallel`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] {s₁ s₂ : 
AffineSubspace k P}, s₁.Parallel s₂ → s₁.direction = s₂.direction
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.map_direction`：map_direction (s : AffineSubspace k P₁) : 
(s.map f).direction = s.direction.map f.linear
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `AffineEquiv.linear_constVAdd`：∀ (k : Type u_1) (P₁ : Type u_2) {V₁ : Typ
e u_6} [inst : Ring k] [inst_1 : AddCommGroup V₁]   [inst_2 : _root_.Module k V₁
] [inst_3 : AddTor…
· 使用定理 `Submodule.map_id`：map_id : map (LinearMap.id : M ->ₗ[R] M) p = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Parallel.direction_eq {s₁ s₂ : AffineSubspace k P} (h : s₁ ∥ s₂) :
    s₁.direction = s₂.direction := by
  rcases h with ⟨v, rfl⟩
  simp

@[simp]
/-
**AffineSubspace.parallel_bot_iff_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspa
ce`。
形式化陈述：parallel_bot_iff_eq_bot {s : AffineSubspace k P} : s ∥ ⊥ ↔ s = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.map_eq_bot_iff`：map_eq_bot_iff {s : AffineSubspace k P₁} 
: s.map f = ⊥ ↔ s = ⊥
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `AffineSubspace.Parallel.refl`：∀ {k : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [i
nst_3 : AddTorsor …
-/
theorem parallel_bot_iff_eq_bot {s : AffineSubspace k P} : s ∥ ⊥ ↔ s = ⊥ := by
  refine ⟨fun h => ?_, fun h => h ▸ Parallel.refl _⟩
  rcases h with ⟨v, h⟩
  rwa [eq_comm, map_eq_bot_iff] at h

@[simp]
/-
**AffineSubspace.bot_parallel_iff_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspa
ce`。
形式化陈述：bot_parallel_iff_eq_bot {s : AffineSubspace k P} : ⊥ ∥ s ↔ s = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.parallel_comm`：parallel_comm {s₁ s₂ : AffineSubspace k P}
 : s₁ ∥ s₂ ↔ s₂ ∥ s₁
· 使用定理 `AffineSubspace.parallel_bot_iff_eq_bot`：parallel_bot_iff_eq_bot {s : Aff
ineSubspace k P} : s ∥ ⊥ ↔ s = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bot_parallel_iff_eq_bot {s : AffineSubspace k P} : ⊥ ∥ s ↔ s = ⊥ := by
  rw [parallel_comm, parallel_bot_iff_eq_bot]
/-
**AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot** 是 Mathlib 中的一
个定理，位于命名空间 `AffineSubspace`。
形式化陈述：parallel_iff_direction_eq_and_eq_bot_iff_eq_bot {s₁ s₂ : AffineSubspace k 
P} : s₁ ∥ s₂ ↔ s₁.direction = s₂.direction ∧ (s₁ = ⊥ ↔ s₂ = ⊥)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.Parallel.direction_eq`：∀ {k : Type u_1} {V : Type u_2} {P
 : Type u_4} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k
 V]   [inst_3 : AddTorsor …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.bot_parallel_iff_eq_bot`：bot_parallel_iff_eq_bot {s : Aff
ineSubspace k P} : ⊥ ∥ s ↔ s = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.parallel_bot_iff_eq_bot`：parallel_bot_iff_eq_bot {s : Aff
ineSubspace k P} : s ∥ ⊥ ↔ s = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AffineSubspace.nonempty_iff_ne_bot`：nonempty_iff_ne_bot (Q : AffineSubsp
ace k P) : (Q : Set P).Nonempty ↔ Q != ⊥
· 使用定理 `AffineSubspace.eq_iff_direction_eq_of_mem`：eq_iff_direction_eq_of_mem {s
₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p in s₁) (h₂ : p in s₂) : s₁ = s₂ ↔ s₁.
direction = s₂.direction
· 使用定理 `AffineSubspace.mem_map`：mem_map {f : P₁ ->ᵃ[k] P₂} {x : P₂} {s : AffineS
ubspace k P₁} : x in s.map f ↔ exists y in s, f y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineEquiv.constVAdd_apply`：∀ (k : Type u_1) (P₁ : Type u_2) {V₁ : Type
 u_6} [inst : Ring k] [inst_1 : AddCommGroup V₁]   [inst_2 : _root_.Module k V₁]
 [inst_3 : AddTor…
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AffineSubspace.map_direction`：map_direction (s : AffineSubspace k P₁) : 
(s.map f).direction = s.direction.map f.linear
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `AffineEquiv.linear_constVAdd`：∀ (k : Type u_1) (P₁ : Type u_2) {V₁ : Typ
e u_6} [inst : Ring k] [inst_1 : AddCommGroup V₁]   [inst_2 : _root_.Module k V₁
] [inst_3 : AddTor…
· 使用定理 `Submodule.map_id`：map_id : map (LinearMap.id : M ->ₗ[R] M) p = p
-/
theorem parallel_iff_direction_eq_and_eq_bot_iff_eq_bot {s₁ s₂ : AffineSubspace k P} :
    s₁ ∥ s₂ ↔ s₁.direction = s₂.direction ∧ (s₁ = ⊥ ↔ s₂ = ⊥) := by
  refine ⟨fun h => ⟨h.direction_eq, ?_, ?_⟩, fun h => ?_⟩
  · rintro rfl
    exact bot_parallel_iff_eq_bot.1 h
  · rintro rfl
    exact parallel_bot_iff_eq_bot.1 h
  · rcases h with ⟨hd, hb⟩
    by_cases hs₁ : s₁ = ⊥
    · rw [hs₁, bot_parallel_iff_eq_bot]
      exact hb.1 hs₁
    · have hs₂ : s₂ ≠ ⊥ := hb.not.1 hs₁
      rcases (nonempty_iff_ne_bot s₁).2 hs₁ with ⟨p₁, hp₁⟩
      rcases (nonempty_iff_ne_bot s₂).2 hs₂ with ⟨p₂, hp₂⟩
      refine ⟨p₂ -ᵥ p₁, (eq_iff_direction_eq_of_mem hp₂ ?_).2 ?_⟩
      · rw [mem_map]
        refine ⟨p₁, hp₁, ?_⟩
        simp
      · simpa using hd.symm
/-
**AffineSubspace.Parallel.vectorSpan_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e.Parallel`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] {s₁ s₂ : 
Set P},   (affineSpan k s₁).Parallel (affineSpan k s₂) → vectorSpan k s₁ = vecto
rSpan k s₂
参数：affineSpan k s₁；affineSpan k s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.Parallel.direction_eq`：∀ {k : Type u_1} {V : Type u_2} {P
 : Type u_4} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k
 V]   [inst_3 : AddTorsor …
-/
theorem Parallel.vectorSpan_eq {s₁ s₂ : Set P} (h : affineSpan k s₁ ∥ affineSpan k s₂) :
    vectorSpan k s₁ = vectorSpan k s₂ := by
  simp_rw [← direction_affineSpan]
  exact h.direction_eq
/-
**AffineSubspace.affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty
** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty {s₁ s₂ : S
et P} : affineSpan k s₁ ∥ affineSpan k s₂ ↔ vectorSpan k s₁ = vectorSpan k s₂ ∧ 
(s₁ = ∅ ↔ s₂ = ∅)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `affineSpan_eq_bot`：affineSpan_eq_bot : affineSpan k s = ⊥ ↔ s = ∅
· 使用定理 `AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot`：parallel
_iff_direction_eq_and_eq_bot_iff_eq_bot {s₁ s₂ : AffineSubspace k P} : s₁ ∥ s₂ ↔
 s₁.direction = s₂.direction ∧ (s₁ = ⊥ ↔ s₂ = ⊥)
-/
theorem affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty {s₁ s₂ : Set P} :
    affineSpan k s₁ ∥ affineSpan k s₂ ↔ vectorSpan k s₁ = vectorSpan k s₂ ∧ (s₁ = ∅ ↔ s₂ = ∅) := by
  repeat rw [← direction_affineSpan, ← affineSpan_eq_bot k]
  exact parallel_iff_direction_eq_and_eq_bot_iff_eq_bot
/-
**AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq** 是 Mathlib 中的一个定理，位
于命名空间 `AffineSubspace`。
形式化陈述：affineSpan_pair_parallel_iff_vectorSpan_eq {p₁ p₂ p₃ p₄ : P} : line[k, p₁,
 p₂] ∥ line[k, p₃, p₄] ↔ vectorSpan k ({p₁, p₂} : Set P) = vectorSpan k ({p₃, p₄
} : Set P)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem affineSpan_pair_parallel_iff_vectorSpan_eq {p₁ p₂ p₃ p₄ : P} :
    line[k, p₁, p₂] ∥ line[k, p₃, p₄] ↔
      vectorSpan k ({p₁, p₂} : Set P) = vectorSpan k ({p₃, p₄} : Set P) := by
  simp [affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty, ←
    not_nonempty_iff_eq_empty]
/-
**AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul'** 是 Mathlib 中的一个
引理，位于命名空间 `AffineSubspace`。
形式化陈述：affineSpan_pair_parallel_iff_exists_unit_smul' [IsDomain k] [Module.IsTors
ionFree k V] {p₁ q₁ p₂ q₂ : P} : line[k, p₁, q₁] ∥ line[k, p₂, q₂] ↔ exists z : 
kˣ, z • (q₁ -ᵥ p₁) = q₂ -ᵥ p₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq`：affineSpan_pa
ir_parallel_iff_vectorSpan_eq {p₁ p₂ p₃ p₄ : P} : line[k, p₁, p₂] ∥ line[k, p₃, 
p₄] ↔ vectorSpan k ({p₁, p₂} : Set P) = vectorS…
· 使用定理 `vectorSpan_pair_rev`：vectorSpan_pair_rev (p₁ p₂ : P) : vectorSpan k ({p₁
, p₂} : Set P) = k ∙ (p₂ -ᵥ p₁)
· 使用定理 `Submodule.span_singleton_eq_span_singleton`：span_singleton_eq_span_singl
eton {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.I
sTorsionFree R M] {x y : M} : (R…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma affineSpan_pair_parallel_iff_exists_unit_smul' [IsDomain k] [Module.IsTorsionFree k V]
    {p₁ q₁ p₂ q₂ : P} :
    line[k, p₁, q₁] ∥ line[k, p₂, q₂] ↔ ∃ z : kˣ, z • (q₁ -ᵥ p₁) = q₂ -ᵥ p₂ := by
  rw [AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq, vectorSpan_pair_rev,
    vectorSpan_pair_rev, Submodule.span_singleton_eq_span_singleton]
/-
**AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul** 是 Mathlib 中的一个引
理，位于命名空间 `AffineSubspace`。
形式化陈述：affineSpan_pair_parallel_iff_exists_unit_smul [IsDomain k] [Module.IsTorsi
onFree k V] {p₁ q₁ p₂ q₂ : P} : line[k, p₁, q₁] ∥ line[k, p₂, q₂] ↔ exists z : k
ˣ, z • (q₂ -ᵥ p₂) = q₁ -ᵥ p₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul'`：affineSpa
n_pair_parallel_iff_exists_unit_smul' [IsDomain k] [Module.IsTorsionFree k V] {p
₁ q₁ p₂ q₂ : P} : line[k, p₁, q₁] ∥ line[k, p₂, q₂]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma affineSpan_pair_parallel_iff_exists_unit_smul [IsDomain k] [Module.IsTorsionFree k V]
    {p₁ q₁ p₂ q₂ : P} :
    line[k, p₁, q₁] ∥ line[k, p₂, q₂] ↔ ∃ z : kˣ, z • (q₂ -ᵥ p₂) = q₁ -ᵥ p₁ := by
  rw [affineSpan_pair_parallel_iff_exists_unit_smul']
  exact ⟨fun ⟨z, hz⟩ ↦ ⟨z⁻¹, by simp [← hz]⟩, fun ⟨z, hz⟩ ↦ ⟨z⁻¹, by simp [← hz]⟩⟩
/-
**AffineSubspace.direction_affineSpan_pair_le_iff_exists_smul** 是 Mathlib 中的一个引理
，位于命名空间 `AffineSubspace`。
形式化陈述：direction_affineSpan_pair_le_iff_exists_smul {p₁ q₁ p₂ q₂ : P} : line[k, p
₁, q₁].direction <= line[k, p₂, q₂].direction ↔ exists z : k, z • (q₂ -ᵥ p₂) = q
₁ -ᵥ p₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `vectorSpan_pair_rev`：vectorSpan_pair_rev (p₁ p₂ : P) : vectorSpan k ({p₁
, p₂} : Set P) = k ∙ (p₂ -ᵥ p₁)
· 使用定理 `Submodule.span_singleton_le_iff_mem`：span_singleton_le_iff_mem (m : M) (
p : Submodule R M) : R ∙ m <= p ↔ m in p
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma direction_affineSpan_pair_le_iff_exists_smul {p₁ q₁ p₂ q₂ : P} :
    line[k, p₁, q₁].direction ≤ line[k, p₂, q₂].direction ↔ ∃ z : k, z • (q₂ -ᵥ p₂) = q₁ -ᵥ p₁ := by
  rw [direction_affineSpan, direction_affineSpan, vectorSpan_pair_rev, vectorSpan_pair_rev,
    Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
/-
**AffineSubspace.affineSpan_pair_comm** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`
。
形式化陈述：affineSpan_pair_comm {p₁ p₂ : P} : line[k, p₁, p₂] = line[k, p₂, p₁]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
-/
theorem affineSpan_pair_comm {p₁ p₂ : P} :
    line[k, p₁, p₂] = line[k, p₂, p₁] := by
  rw [Set.pair_comm]

end AffineSubspace

section DivisionRing

open AffineSubspace

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- The span of two different points that lie in a line through two points equals that line. -/
/-
**affineSpan_pair_eq_of_mem_of_mem_of_ne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：affineSpan_pair_eq_of_mem_of_mem_of_ne {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ in line
[k, p₃, p₄]) (hp₂ : p₂ in line[k, p₃, p₄]) (hp₁₂ : p₁ != p₂) : line[k, p₁, p₂] =
 line[k, p₃, p₄]
参数：hp₁ : p₁ in line[k, p₃, p₄]；hp₂ : p₂ in line[k, p₃, p₄]；hp₁₂ : p₁ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `affineSpan_pair_le_of_mem_of_mem`：affineSpan_pair_le_of_mem_of_mem {p₁ p
₂ : P} {s : AffineSubspace k P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : line[k, p₁, p₂
] <= s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_left_mem_affineSpan_pair`：vadd_left_mem_affineSpan_pair {p₁ p₂ : P}
 {v : V} : v +ᵥ p₁ in line[k, p₁, p₂] ↔ exists r : k, r • (p₂ -ᵥ p₁) = v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `eq_inv_smul_iff₀`：eq_inv_smul_iff₀ (ha : a != 0) {x y : β} : x = a⁻¹ • y
 ↔ a • x = y
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `smul_vsub_vadd_mem_affineSpan_pair`：smul_vsub_vadd_mem_affineSpan_pair (
r : k) (p₁ p₂ : P) : r • (p₂ -ᵥ p₁) +ᵥ p₁ in line[k, p₁, p₂]
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
The span of two different points that lie in a line through two points equals th
at line.
-/
lemma affineSpan_pair_eq_of_mem_of_mem_of_ne {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ ∈ line[k, p₃, p₄])
    (hp₂ : p₂ ∈ line[k, p₃, p₄]) (hp₁₂ : p₁ ≠ p₂) : line[k, p₁, p₂] = line[k, p₃, p₄] := by
  refine le_antisymm (affineSpan_pair_le_of_mem_of_mem hp₁ hp₂) ?_
  rw [← vsub_vadd p₁ p₃, vadd_left_mem_affineSpan_pair] at hp₁
  rcases hp₁ with ⟨r₁, hp₁⟩
  rw [← vsub_vadd p₂ p₃, vadd_left_mem_affineSpan_pair] at hp₂
  rcases hp₂ with ⟨r₂, hp₂⟩
  have hr₀ : r₂ - r₁ ≠ 0 := by
    rw [sub_ne_zero]
    rintro rfl
    simp_all
  have hr : (r₂ - r₁) • (p₄ -ᵥ p₃) = p₂ -ᵥ p₁ := by
    simp [sub_smul, hp₁, hp₂]
  rw [← eq_inv_smul_iff₀ hr₀] at hr
  refine affineSpan_pair_le_of_mem_of_mem ?_ ?_
  · convert! smul_vsub_vadd_mem_affineSpan_pair (-r₁ * (r₂ - r₁)⁻¹) p₁ p₂
    simp [mul_smul, ← hr, hp₁]
  · convert! smul_vsub_vadd_mem_affineSpan_pair ((1 - r₁) * (r₂ - r₁)⁻¹) p₁ p₂
    simp [mul_smul, ← hr, sub_smul, hp₁]

/-- One line equals another differing in the first point if the first point of the first line is
contained in the second line and does not equal the second point. -/
/-
**affineSpan_pair_eq_of_left_mem_of_ne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：affineSpan_pair_eq_of_left_mem_of_ne {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂,
 p₃]) (hne : p₁ != p₃) : line[k, p₁, p₃] = line[k, p₂, p₃]
参数：h : p₁ in line[k, p₂, p₃]；hne : p₁ != p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `affineSpan_pair_eq_of_mem_of_mem_of_ne`：affineSpan_pair_eq_of_mem_of_mem
_of_ne {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ in line[k, p₃, p₄]) (hp₂ : p₂ in line[k, p₃, 
p₄]) (hp₁₂ : p₁ != p₂) : lin…
· 使用定理 `right_mem_affineSpan_pair`：right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ in
 line[k, p₁, p₂]

--- 原说明 ---
One line equals another differing in the first point if the first point of the f
irst line is
contained in the second line and does not equal the second point.
-/
lemma affineSpan_pair_eq_of_left_mem_of_ne {p₁ p₂ p₃ : P} (h : p₁ ∈ line[k, p₂, p₃])
    (hne : p₁ ≠ p₃) : line[k, p₁, p₃] = line[k, p₂, p₃] :=
  affineSpan_pair_eq_of_mem_of_mem_of_ne h (right_mem_affineSpan_pair _ _ _) hne

/-- One line equals another differing in the second point if the second point of the first line is
contained in the second line and does not equal the first point. -/
/-
**affineSpan_pair_eq_of_right_mem_of_ne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：affineSpan_pair_eq_of_right_mem_of_ne {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂
, p₃]) (hne : p₁ != p₂) : line[k, p₂, p₁] = line[k, p₂, p₃]
参数：h : p₁ in line[k, p₂, p₃]；hne : p₁ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `affineSpan_pair_eq_of_mem_of_mem_of_ne`：affineSpan_pair_eq_of_mem_of_mem
_of_ne {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ in line[k, p₃, p₄]) (hp₂ : p₂ in line[k, p₃, 
p₄]) (hp₁₂ : p₁ != p₂) : lin…
· 使用定理 `left_mem_affineSpan_pair`：left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in l
ine[k, p₁, p₂]
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
One line equals another differing in the second point if the second point of the
 first line is
contained in the second line and does not equal the first point.
-/
lemma affineSpan_pair_eq_of_right_mem_of_ne {p₁ p₂ p₃ : P} (h : p₁ ∈ line[k, p₂, p₃])
    (hne : p₁ ≠ p₂) :
    line[k, p₂, p₁] = line[k, p₂, p₃] :=
  affineSpan_pair_eq_of_mem_of_mem_of_ne (left_mem_affineSpan_pair _ _ _) h hne.symm

/-- Given two triples of non-collinear points, if the lines determined by corresponding pairs of
points are parallel, then the vectors between corresponding pairs of points are all related by the
same nonzero scale factor. (The formal statement is slightly more general.) -/
/-
**exists_eq_smul_of_parallel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_eq_smul_of_parallel {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h₂ : p₂ ∉ line[k, p₁, 
p₃]) (h₁₂₄₅ : line[k, p₁, p₂] ∥ line[k, p₄, p₅]) (h₂₃₅₆ : line[k, p₅, p₆].direct
ion <= line[k, p₂, p₃].direction) (h₃₁₆₄ : line[k, p₆, p₄].direction <= line[k, 
p₃, p₁].direction) : exists r : k, r != 0 ∧ p₅ -ᵥ p₄ = r • (p₂ -ᵥ p₁) ∧ p₆ -ᵥ p₅
 = r • (p₃ -ᵥ p₂) ∧ p₄ -ᵥ p₆ = r • (p₁ -ᵥ p₃)
参数：h₂ : p₂ ∉ line[k, p₁, p₃]；h₁₂₄₅ : line[k, p₁, p₂] ∥ line[k, p₄, p₅]；h₂₃₅₆ : l
ine[k, p₅, p₆].direction <= line[k, p₂, p₃].direction；h₃₁₆₄ : line[k, p₆, p₄].di
rection <= line[k, p₃, p₁].direction。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul'`：affineSpa
n_pair_parallel_iff_exists_unit_smul' [IsDomain k] [Module.IsTorsionFree k V] {p
₁ q₁ p₂ q₂ : P} : line[k, p₁, q₁] ∥ line[k, p₂, q₂]…
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `AffineSubspace.direction_affineSpan_pair_le_iff_exists_smul`：direction_a
ffineSpan_pair_le_iff_exists_smul {p₁ q₁ p₂ q₂ : P} : line[k, p₁, q₁].direction 
<= line[k, p₂, q₂].direction ↔ exists z : k, z • …
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `smul_vsub_mem_vectorSpan_pair`：smul_vsub_mem_vectorSpan_pair (r : k) (p₁
 p₂ : P) : r • (p₁ -ᵥ p₂) in vectorSpan k ({p₁, p₂} : Set P)
· 使用定理 `smul_vsub_rev_mem_vectorSpan_pair`：smul_vsub_rev_mem_vectorSpan_pair (r 
: k) (p₁ p₂ : P) : r • (p₂ -ᵥ p₁) in vectorSpan k ({p₁, p₂} : Set P)
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `add_sub_add_left_eq_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c + a - (c + b) = a - b
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `AffineSubspace.vsub_left_mem_direction_iff_mem`：vsub_left_mem_direction_
iff_mem {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P) : p -ᵥ p₂ in s.d
irection ↔ p₂ in s
· 使用定理 `right_mem_affineSpan_pair`：right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ in
 line[k, p₁, p₂]
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a

--- 原说明 ---
Given two triples of non-collinear points, if the lines determined by correspond
ing pairs of
points are parallel, then the vectors between corresponding pairs of points are 
all related by the
same nonzero scale factor. (The formal statement is slightly more general.)
-/
theorem exists_eq_smul_of_parallel {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h₂ : p₂ ∉ line[k, p₁, p₃])
    (h₁₂₄₅ : line[k, p₁, p₂] ∥ line[k, p₄, p₅])
    (h₂₃₅₆ : line[k, p₅, p₆].direction ≤ line[k, p₂, p₃].direction)
    (h₃₁₆₄ : line[k, p₆, p₄].direction ≤ line[k, p₃, p₁].direction) :
    ∃ r : k, r ≠ 0 ∧ p₅ -ᵥ p₄ = r • (p₂ -ᵥ p₁) ∧ p₆ -ᵥ p₅ = r • (p₃ -ᵥ p₂) ∧
      p₄ -ᵥ p₆ = r • (p₁ -ᵥ p₃) := by
  rw [affineSpan_pair_parallel_iff_exists_unit_smul'] at h₁₂₄₅
  rw [direction_affineSpan_pair_le_iff_exists_smul] at h₂₃₅₆ h₃₁₆₄
  obtain ⟨r₁, hr₁⟩ := h₁₂₄₅
  obtain ⟨r₂, hr₂⟩ := h₂₃₅₆
  obtain ⟨r₃, hr₃⟩ := h₃₁₆₄
  rw [Units.smul_def] at hr₁
  by_cases h : (r₁ : k) = r₂
  · refine ⟨r₁, r₁.ne_zero, hr₁.symm, h ▸ hr₂.symm, ?_⟩
    rw [← neg_inj, neg_vsub_eq_vsub_rev, ← smul_neg, neg_vsub_eq_vsub_rev,
      ← vsub_add_vsub_cancel p₆ p₅ p₄, ← vsub_add_vsub_cancel p₃ p₂ p₁, smul_add, hr₁, h, hr₂]
  · exfalso
    have h₁₂ : (r₁ : k) • (p₂ -ᵥ p₁) + r₂ • (p₃ -ᵥ p₂) ∈ vectorSpan k {p₁, p₃} := by
      rw [hr₁, hr₂, add_comm, vsub_add_vsub_cancel, ← neg_vsub_eq_vsub_rev, neg_mem_iff, ← hr₃]
      exact smul_vsub_mem_vectorSpan_pair _ _ _
    have h₁₁ : (r₁ : k) • (p₂ -ᵥ p₁) + (r₁ : k) • (p₃ -ᵥ p₂) ∈ vectorSpan k {p₁, p₃} := by
      rw [add_comm, ← smul_add, vsub_add_vsub_cancel]
      exact smul_vsub_rev_mem_vectorSpan_pair _ _ _
    have h₂₁ : (r₂ - r₁) • (p₃ -ᵥ p₂) ∈ vectorSpan k {p₁, p₃} := by
      simpa [sub_smul] using sub_mem h₁₂ h₁₁
    rw [Submodule.smul_mem_iff _ (by rwa [sub_ne_zero, ne_comm]), ← direction_affineSpan,
      vsub_left_mem_direction_iff_mem (right_mem_affineSpan_pair _ _ _)] at h₂₁
    exact h₂ h₂₁

end DivisionRing

