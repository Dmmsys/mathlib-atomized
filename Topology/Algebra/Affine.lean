/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Attila Gáspár
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Topology.Algebra.Group.Torsor

/-!
# Topological properties of affine spaces and maps

This file contains a few facts regarding the continuity of affine maps.
-/

public section


namespace AffineMap

variable
  {R V P W Q : Type*}
  [AddCommGroup V] [TopologicalSpace V]
  [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P]
  [AddCommGroup W] [TopologicalSpace W]
  [AddTorsor W Q] [TopologicalSpace Q] [IsTopologicalAddTorsor Q]

section Ring

variable [Ring R] [Module R V] [Module R W]

/-- If `f` is an affine map, then its linear part is continuous iff `f` is continuous. -/
/-
**AffineMap.continuous_linear_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：continuous_linear_iff {f : P ->ᵃ[R] Q} : Continuous f.linear ↔ Continuous 
f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.vaddConst_apply`：∀ {V : Type u_1} {P : Type u_2} [inst : AddG
roup V] [inst_1 : TopologicalSpace V] [inst_2 : AddTorsor V P]   [inst_3 : Topol
ogicalSpace P] […
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `Homeomorph.vaddConst_symm_apply`：∀ {V : Type u_1} {P : Type u_2} [inst :
 AddGroup V] [inst_1 : TopologicalSpace V] [inst_2 : AddTorsor V P]   [inst_3 : 
TopologicalSpace P] […
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f` is an affine map, then its linear part is continuous iff `f` is continuou
s.
-/
theorem continuous_linear_iff {f : P →ᵃ[R] Q} : Continuous f.linear ↔ Continuous f := by
  inhabit P
  have :
    (f.linear : V → W) =
      (Homeomorph.vaddConst <| f default).symm ∘ f ∘ (Homeomorph.vaddConst default) := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_continuous_iff, Homeomorph.comp_continuous_iff']

/-- If `f` is an affine map, then its linear part is an open map iff `f` is an open map. -/
/-
**AffineMap.isOpenMap_linear_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：isOpenMap_linear_iff {f : P ->ᵃ[R] Q} : IsOpenMap f.linear ↔ IsOpenMap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.vaddConst_apply`：∀ {V : Type u_1} {P : Type u_2} [inst : AddG
roup V] [inst_1 : TopologicalSpace V] [inst_2 : AddTorsor V P]   [inst_3 : Topol
ogicalSpace P] […
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `Homeomorph.vaddConst_symm_apply`：∀ {V : Type u_1} {P : Type u_2} [inst :
 AddGroup V] [inst_1 : TopologicalSpace V] [inst_2 : AddTorsor V P]   [inst_3 : 
TopologicalSpace P] […
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f` is an affine map, then its linear part is an open map iff `f` is an open 
map.
-/
theorem isOpenMap_linear_iff {f : P →ᵃ[R] Q} : IsOpenMap f.linear ↔ IsOpenMap f := by
  inhabit P
  have :
    (f.linear : V → W) =
      (Homeomorph.vaddConst <| f default).symm ∘ f ∘ (Homeomorph.vaddConst default) := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_isOpenMap_iff, Homeomorph.comp_isOpenMap_iff']

variable [TopologicalSpace R] [ContinuousSMul R V]

set_option backward.isDefEq.respectTransparency false in
/-- The line map is continuous in all arguments. -/
@[continuity, fun_prop]
/-
**AffineMap.lineMap_continuous_uncurry** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_continuous_uncurry : Continuous (fun pqt : P × P × R => lineMap pq
t.1 pqt.2.1 pqt.2.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.fun_vadd`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsTopologicalAddTorsor.toContinuousVAdd`：∀ {V : Type u_1} {inst : AddGro
up V} {inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : AddTorsor V P}   {i
nst_3 : TopologicalSpace P} […
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.vsub`：∀ {V : Type u_1} {P : Type u_2} {α : Type u_3} [inst : 
AddGroup V] [inst_1 : TopologicalSpace V]   [inst_2 : AddTorsor V P] [inst_3 : T
opolo…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1

--- 原说明 ---
The line map is continuous in all arguments.
-/
theorem lineMap_continuous_uncurry :
    Continuous (fun pqt : P × P × R ↦ lineMap pqt.1 pqt.2.1 pqt.2.2) := by
  simp only [coe_lineMap]
  fun_prop

/-- The line map is continuous. -/
/-
**AffineMap.lineMap_continuous** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_continuous {p q : P} : Continuous (lineMap p q : R ->ᵃ[R] P)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `AffineMap.lineMap_continuous_uncurry`：lineMap_continuous_uncurry : Conti
nuous (fun pqt : P × P × R => lineMap pqt.1 pqt.2.1 pqt.2.2)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)

--- 原说明 ---
The line map is continuous.
-/
theorem lineMap_continuous {p q : P} :
    Continuous (lineMap p q : R →ᵃ[R] P) := by
  fun_prop

open Topology Filter

section Tendsto

variable {α : Type*} {l : Filter α}

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap._root_.Filter.Tendsto.lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.Tendsto.lineMap {f₁ f₂ : α → P} {g : α → R} {p₁ p₂ : P} {c : R}
    (h₁ : Tendsto f₁ l (𝓝 p₁)) (h₂ : Tendsto f₂ l (𝓝 p₂)) (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun x => AffineMap.lineMap (f₁ x) (f₂ x) (g x)) l (𝓝 <| AffineMap.lineMap p₁ p₂ c) :=
  (hg.smul (h₂.vsub h₁)).vadd h₁
/-
**AffineMap._root_.Filter.Tendsto.midpoint** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.Tendsto.midpoint [Invertible (2 : R)] {f₁ f₂ : α → P} {p₁ p₂ : P}
    (h₁ : Tendsto f₁ l (𝓝 p₁)) (h₂ : Tendsto f₂ l (𝓝 p₂)) :
    Tendsto (fun x => midpoint R (f₁ x) (f₂ x)) l (𝓝 <| midpoint R p₁ p₂) :=
  h₁.lineMap h₂ tendsto_const_nhds

end Tendsto

variable {X : Type*} [TopologicalSpace X] {f₁ f₂ : X → P} {g : X → R} {s : Set X} {x : X}

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
/-
**AffineMap._root_.ContinuousWithinAt.lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineM
ap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousWithinAt.lineMap (h₁ : ContinuousWithinAt f₁ s x)
    (h₂ : ContinuousWithinAt f₂ s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x ↦ lineMap (f₁ x) (f₂ x) (g x)) s x :=
  Tendsto.lineMap h₁ h₂ hg

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap._root_.ContinuousAt.lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousAt.lineMap (h₁ : ContinuousAt f₁ x) (h₂ : ContinuousAt f₂ x)
    (hg : ContinuousAt g x) :
    ContinuousAt (fun x ↦ lineMap (f₁ x) (f₂ x) (g x)) x := by
  fun_prop

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap._root_.ContinuousOn.lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousOn.lineMap (h₁ : ContinuousOn f₁ s) (h₂ : ContinuousOn f₂ s)
    (hg : ContinuousOn g s) :
    ContinuousOn (fun x ↦ lineMap (f₁ x) (f₂ x) (g x)) s := by
  fun_prop

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap._root_.Continuous.lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.lineMap (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (hg : Continuous g) :
    Continuous (fun x ↦ lineMap (f₁ x) (f₂ x) (g x)) := by
  fun_prop

end Ring

section CommRing

variable [CommRing R] [Module R V] [ContinuousConstSMul R V]

@[continuity, fun_prop]
/-
**AffineMap.homothety_continuous** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_continuous (x : P) (t : R) : Continuous homothety x t
参数：x : P；t : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.coe_homothety`：coe_homothety (c : P1) (r : k) : homothety c r 
= fun p => r • (p -ᵥ c) +ᵥ c
· 使用定理 `Continuous.fun_vadd`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsTopologicalAddTorsor.toContinuousVAdd`：∀ {V : Type u_1} {inst : AddGro
up V} {inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : AddTorsor V P}   {i
nst_3 : TopologicalSpace P} […
· 使用定理 `Continuous.fun_const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type u_3
} [inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α]   [i
nst_3 : Topolog…
· 使用定理 `Continuous.vsub`：∀ {V : Type u_1} {P : Type u_2} {α : Type u_3} [inst : 
AddGroup V] [inst_1 : TopologicalSpace V]   [inst_2 : AddTorsor V P] [inst_3 : T
opolo…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem homothety_continuous (x : P) (t : R) : Continuous <| homothety x t := by
  rw [coe_homothety]
  fun_prop

variable (R) [TopologicalSpace R] [Module R W] [ContinuousSMul R W] (x : Q) {s : Set Q}

open Topology
/-
**AffineMap._root_.eventually_homothety_mem_of_mem_interior** 是 Mathlib 中的一个定理，位
于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.eventually_homothety_mem_of_mem_interior {y : Q} (hy : y ∈ interior s) :
    ∀ᶠ δ in 𝓝 (1 : R), homothety x δ y ∈ s := by
  have cont : Continuous (fun δ : R => homothety x δ y) := lineMap_continuous
  filter_upwards [cont.tendsto' 1 y (by simp) |>.eventually (isOpen_interior.eventually_mem hy)]
    with _ h using interior_subset h
/-
**AffineMap._root_.eventually_homothety_image_subset_of_finite_subset_interior**
 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.eventually_homothety_image_subset_of_finite_subset_interior {t : Set Q}
    (ht : t.Finite) (h : t ⊆ interior s) : ∀ᶠ δ in 𝓝 (1 : R), homothety x δ '' t ⊆ s := by
  suffices ∀ y ∈ t, ∀ᶠ δ in 𝓝 (1 : R), homothety x δ y ∈ s by
    simp_rw [Set.image_subset_iff]
    exact (Filter.eventually_all_finite ht).mpr this
  intro y hy
  exact eventually_homothety_mem_of_mem_interior R x (h hy)

end CommRing

section Field

variable [Field R] [Module R V] [ContinuousConstSMul R V]

/-
**AffineMap.homothety_isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_isOpenMap (x : P) (t : R) (ht : t != 0) : IsOpenMap homothety x 
t
参数：x : P；t : R；ht : t != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.of_inverse`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f' : Y → X},   Continuous f
' → Functi…
· 使用定理 `AffineMap.homothety_continuous`：homothety_continuous (x : P) (t : R) : C
ontinuous homothety x t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AffineMap.homothety_one`：homothety_one (c : P1) : homothety c (1 : k) = 
id k P1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
-/
theorem homothety_isOpenMap (x : P) (t : R) (ht : t ≠ 0) : IsOpenMap <| homothety x t := by
  apply IsOpenMap.of_inverse (homothety_continuous x t⁻¹) <;> intro e <;>
    simp [← AffineMap.comp_apply, ← homothety_mul, ht]

end Field

end AffineMap

