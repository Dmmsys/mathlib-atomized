/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Sides of affine subspaces

This file defines notions of two points being on the same or opposite sides of an affine subspace.

## Main definitions

* `s.WSameSide x y`: The points `x` and `y` are weakly on the same side of the affine
  subspace `s`.
* `s.SSameSide x y`: The points `x` and `y` are strictly on the same side of the affine
  subspace `s`.
* `s.WOppSide x y`: The points `x` and `y` are weakly on opposite sides of the affine
  subspace `s`.
* `s.SOppSide x y`: The points `x` and `y` are strictly on opposite sides of the affine
  subspace `s`.

-/

@[expose] public section


variable {R V V' P P' : Type*}

open AffineEquiv AffineMap

namespace AffineSubspace

section StrictOrderedCommRing

variable [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

/-- The points `x` and `y` are weakly on the same side of `s`. -/
/-
**AffineSubspace.WSameSide** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：WSameSide (s : AffineSubspace R P) (x y : P) : Prop
参数：s : AffineSubspace R P；x y : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The points `x` and `y` are weakly on the same side of `s`.
-/
def WSameSide (s : AffineSubspace R P) (x y : P) : Prop :=
  ∃ᵉ (p₁ ∈ s) (p₂ ∈ s), SameRay R (x -ᵥ p₁) (y -ᵥ p₂)

/-- The points `x` and `y` are strictly on the same side of `s`. -/
/-
**AffineSubspace.SSameSide** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：SSameSide (s : AffineSubspace R P) (x y : P) : Prop
参数：s : AffineSubspace R P；x y : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The points `x` and `y` are strictly on the same side of `s`.
-/
def SSameSide (s : AffineSubspace R P) (x y : P) : Prop :=
  s.WSameSide x y ∧ x ∉ s ∧ y ∉ s

/-- The points `x` and `y` are weakly on opposite sides of `s`. -/
/-
**AffineSubspace.WOppSide** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：WOppSide (s : AffineSubspace R P) (x y : P) : Prop
参数：s : AffineSubspace R P；x y : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The points `x` and `y` are weakly on opposite sides of `s`.
-/
def WOppSide (s : AffineSubspace R P) (x y : P) : Prop :=
  ∃ᵉ (p₁ ∈ s) (p₂ ∈ s), SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)

/-- The points `x` and `y` are strictly on opposite sides of `s`. -/
/-
**AffineSubspace.SOppSide** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：SOppSide (s : AffineSubspace R P) (x y : P) : Prop
参数：s : AffineSubspace R P；x y : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The points `x` and `y` are strictly on opposite sides of `s`.
-/
def SOppSide (s : AffineSubspace R P) (x y : P) : Prop :=
  s.WOppSide x y ∧ x ∉ s ∧ y ∉ s
/-
**AffineSubspace.WSameSide.map** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.WSameSi
de`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {V' : Type u_3} {P : Type u_4} {P' : Type 
u_5} [inst : CommRing R]   [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : AddCommGroup V] [inst_4 : _root_.Module R V]   [inst_5 : AddTors
or V P] [inst_6 : AddCommGroup V'] [inst_7 : _root_.Module R V'] [inst_8 : AddTo
rsor V' P']   {s : AffineSubspace R P} {x y : P},   s.WSameSide x y → ∀ (f : P →
ᵃ[R] P'), (AffineSubspace.map f s).WSameSide (f x) (f y)
参数：f : P →ᵃ[R] P'；AffineSubspace.map f s；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.mem_map_of_mem`：mem_map_of_mem {x : P₁} {s : AffineSubspa
ce k P₁} (h : x in s) : f x in s.map f
· 使用定理 `SameRay.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1 : P
artialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid…
· 使用定理 `SameRay.map`：map (f : M ->ₗ[R] N) (h : SameRay R x y) : SameRay R (f x) 
(f y)
-/
theorem WSameSide.map {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) (f : P →ᵃ[R] P') :
    (s.map f).WSameSide (f x) (f y) := by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  refine ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, ?_⟩
  simp_rw [← linearMap_vsub]
  exact h.map f.linear
/-
**AffineSubspace._root_.Function.Injective.wSameSide_map_iff** 是 Mathlib 中的一个定理，
位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Injective.wSameSide_map_iff {s : AffineSubspace R P} {x y : P}
    {f : P →ᵃ[R] P'} (hf : Function.Injective f) :
    (s.map f).WSameSide (f x) (f y) ↔ s.WSameSide x y := by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  rw [mem_map] at hfp₁ hfp₂
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  simp_rw [← linearMap_vsub, (f.linear_injective_iff.2 hf).sameRay_map_iff] at h
  exact h
/-
**AffineSubspace._root_.Function.Injective.sSameSide_map_iff** 是 Mathlib 中的一个定理，
位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Injective.sSameSide_map_iff {s : AffineSubspace R P} {x y : P}
    {f : P →ᵃ[R] P'} (hf : Function.Injective f) :
    (s.map f).SSameSide (f x) (f y) ↔ s.SSameSide x y := by
  simp_rw [SSameSide, hf.wSameSide_map_iff, mem_map_iff_mem_of_injective hf]

@[simp]
/-
**AffineSubspace._root_.AffineEquiv.wSameSide_map_iff** 是 Mathlib 中的一个定理，位于命名空间 
`AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AffineEquiv.wSameSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).WSameSide (f x) (f y) ↔ s.WSameSide x y :=
  (show Function.Injective f.toAffineMap from f.injective).wSameSide_map_iff

@[simp]
/-
**AffineSubspace._root_.AffineEquiv.sSameSide_map_iff** 是 Mathlib 中的一个定理，位于命名空间 
`AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AffineEquiv.sSameSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).SSameSide (f x) (f y) ↔ s.SSameSide x y :=
  (show Function.Injective f.toAffineMap from f.injective).sSameSide_map_iff
/-
**AffineSubspace.WOppSide.map** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.WOppSide
`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {V' : Type u_3} {P : Type u_4} {P' : Type 
u_5} [inst : CommRing R]   [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : AddCommGroup V] [inst_4 : _root_.Module R V]   [inst_5 : AddTors
or V P] [inst_6 : AddCommGroup V'] [inst_7 : _root_.Module R V'] [inst_8 : AddTo
rsor V' P']   {s : AffineSubspace R P} {x y : P}, s.WOppSide x y → ∀ (f : P →ᵃ[R
] P'), (AffineSubspace.map f s).WOppSide (f x) (f y)
参数：f : P →ᵃ[R] P'；AffineSubspace.map f s；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.mem_map_of_mem`：mem_map_of_mem {x : P₁} {s : AffineSubspa
ce k P₁} (h : x in s) : f x in s.map f
· 使用定理 `SameRay.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1 : P
artialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid…
· 使用定理 `SameRay.map`：map (f : M ->ₗ[R] N) (h : SameRay R x y) : SameRay R (f x) 
(f y)
-/
theorem WOppSide.map {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) (f : P →ᵃ[R] P') :
    (s.map f).WOppSide (f x) (f y) := by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  refine ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, ?_⟩
  simp_rw [← linearMap_vsub]
  exact h.map f.linear
/-
**AffineSubspace._root_.Function.Injective.wOppSide_map_iff** 是 Mathlib 中的一个定理，位
于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Injective.wOppSide_map_iff {s : AffineSubspace R P} {x y : P}
    {f : P →ᵃ[R] P'} (hf : Function.Injective f) :
    (s.map f).WOppSide (f x) (f y) ↔ s.WOppSide x y := by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  rw [mem_map] at hfp₁ hfp₂
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  simp_rw [← linearMap_vsub, (f.linear_injective_iff.2 hf).sameRay_map_iff] at h
  exact h
/-
**AffineSubspace._root_.Function.Injective.sOppSide_map_iff** 是 Mathlib 中的一个定理，位
于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Injective.sOppSide_map_iff {s : AffineSubspace R P} {x y : P}
    {f : P →ᵃ[R] P'} (hf : Function.Injective f) :
    (s.map f).SOppSide (f x) (f y) ↔ s.SOppSide x y := by
  simp_rw [SOppSide, hf.wOppSide_map_iff, mem_map_iff_mem_of_injective hf]

@[simp]
/-
**AffineSubspace._root_.AffineEquiv.wOppSide_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `
AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AffineEquiv.wOppSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).WOppSide (f x) (f y) ↔ s.WOppSide x y :=
  (show Function.Injective f.toAffineMap from f.injective).wOppSide_map_iff

@[simp]
/-
**AffineSubspace._root_.AffineEquiv.sOppSide_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `
AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AffineEquiv.sOppSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).SOppSide (f x) (f y) ↔ s.SOppSide x y :=
  (show Function.Injective f.toAffineMap from f.injective).sOppSide_map_iff
/-
**AffineSubspace.WSameSide.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.WS
ameSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : CommRing R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] 
[inst_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P}
 {x y : P}, s.WSameSide x y → (↑s).Nonempty
参数：↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem WSameSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.choose, h.choose_spec.left⟩
/-
**AffineSubspace.SSameSide.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.SS
ameSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : CommRing R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] 
[inst_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P}
 {x y : P}, s.SSameSide x y → (↑s).Nonempty
参数：↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem SSameSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.1.choose, h.1.choose_spec.left⟩
/-
**AffineSubspace.WOppSide.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.WOp
pSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : CommRing R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] 
[inst_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P}
 {x y : P}, s.WOppSide x y → (↑s).Nonempty
参数：↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem WOppSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.choose, h.choose_spec.left⟩
/-
**AffineSubspace.SOppSide.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.SOp
pSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : CommRing R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] 
[inst_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P}
 {x y : P}, s.SOppSide x y → (↑s).Nonempty
参数：↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem SOppSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.1.choose, h.1.choose_spec.left⟩
/-
**AffineSubspace.SSameSide.wSameSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.S
SameSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : CommRing R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] 
[inst_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P}
 {x y : P}, s.SSameSide x y → s.WSameSide x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem SSameSide.wSameSide {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    s.WSameSide x y :=
  h.1
/-
**AffineSubspace.SSameSide.left_notMem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
.SSameSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : CommRing R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] 
[inst_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P}
 {x y : P}, s.SSameSide x y → x ∉ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem SSameSide.left_notMem {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) : x ∉ s :=
  h.2.1
/-
**AffineSubspace.SSameSide.right_notMem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e.SSameSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : CommRing R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] 
[inst_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P}
 {x y : P}, s.SSameSide x y → y ∉ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem SSameSide.right_notMem {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) : y ∉ s :=
  h.2.2
/-
**AffineSubspace.SOppSide.wOppSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.SOp
pSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : CommRing R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] 
[inst_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P}
 {x y : P}, s.SOppSide x y → s.WOppSide x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem SOppSide.wOppSide {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    s.WOppSide x y :=
  h.1
/-
**AffineSubspace.SOppSide.left_notMem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.
SOppSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : CommRing R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] 
[inst_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P}
 {x y : P}, s.SOppSide x y → x ∉ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem SOppSide.left_notMem {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) : x ∉ s :=
  h.2.1
/-
**AffineSubspace.SOppSide.right_notMem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
.SOppSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : CommRing R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] 
[inst_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P}
 {x y : P}, s.SOppSide x y → y ∉ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem SOppSide.right_notMem {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) : y ∉ s :=
  h.2.2
/-
**AffineSubspace.wSameSide_comm** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：wSameSide_comm {s : AffineSubspace R P} {x y : P} : s.WSameSide x y ↔ s.WS
ameSide y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.symm`：symm (h : SameRay R x y) : SameRay R y x
-/
theorem wSameSide_comm {s : AffineSubspace R P} {x y : P} : s.WSameSide x y ↔ s.WSameSide y x :=
  ⟨fun ⟨p₁, hp₁, p₂, hp₂, h⟩ => ⟨p₂, hp₂, p₁, hp₁, h.symm⟩,
    fun ⟨p₁, hp₁, p₂, hp₂, h⟩ => ⟨p₂, hp₂, p₁, hp₁, h.symm⟩⟩

alias ⟨WSameSide.symm, _⟩ := wSameSide_comm
/-
**AffineSubspace.sSameSide_comm** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：sSameSide_comm {s : AffineSubspace R P} {x y : P} : s.SSameSide x y ↔ s.SS
ameSide y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.SSameSide.eq_1`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.wSameSide_comm`：wSameSide_comm {s : AffineSubspace R P} {
x y : P} : s.WSameSide x y ↔ s.WSameSide y x
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sSameSide_comm {s : AffineSubspace R P} {x y : P} : s.SSameSide x y ↔ s.SSameSide y x := by
  rw [SSameSide, SSameSide, wSameSide_comm, and_comm (b := x ∉ s)]

alias ⟨SSameSide.symm, _⟩ := sSameSide_comm
/-
**AffineSubspace.wOppSide_comm** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：wOppSide_comm {s : AffineSubspace R P} {x y : P} : s.WOppSide x y ↔ s.WOpp
Side y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SameRay.sameRay_comm`：sameRay_comm : SameRay R x y ↔ SameRay R y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sameRay_neg_iff`：sameRay_neg_iff : SameRay R (-x) (-y) ↔ SameRay R x y
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
-/
theorem wOppSide_comm {s : AffineSubspace R P} {x y : P} : s.WOppSide x y ↔ s.WOppSide y x := by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]

alias ⟨WOppSide.symm, _⟩ := wOppSide_comm
/-
**AffineSubspace.sOppSide_comm** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：sOppSide_comm {s : AffineSubspace R P} {x y : P} : s.SOppSide x y ↔ s.SOpp
Side y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.SOppSide.eq_1`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.wOppSide_comm`：wOppSide_comm {s : AffineSubspace R P} {x 
y : P} : s.WOppSide x y ↔ s.WOppSide y x
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sOppSide_comm {s : AffineSubspace R P} {x y : P} : s.SOppSide x y ↔ s.SOppSide y x := by
  rw [SOppSide, SOppSide, wOppSide_comm, and_comm (b := x ∉ s)]

alias ⟨SOppSide.symm, _⟩ := sOppSide_comm
/-
**AffineSubspace.not_wSameSide_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：not_wSameSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).WSameSide x y
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_wSameSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).WSameSide x y :=
  fun ⟨_, h, _⟩ => h.elim
/-
**AffineSubspace.not_sSameSide_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：not_sSameSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).SSameSide x y
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.not_wSameSide_bot`：not_wSameSide_bot (x y : P) : ¬(⊥ : Af
fineSubspace R P).WSameSide x y
· 使用定理 `AffineSubspace.SSameSide.wSameSide`：∀ {R : Type u_1} {V : Type u_2} {P :
 Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrd
eredRing R] [inst_3 : Ad…
-/
theorem not_sSameSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).SSameSide x y :=
  fun h => not_wSameSide_bot x y h.wSameSide
/-
**AffineSubspace.not_wOppSide_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：not_wOppSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).WOppSide x y
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_wOppSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).WOppSide x y :=
  fun ⟨_, h, _⟩ => h.elim
/-
**AffineSubspace.not_sOppSide_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：not_sOppSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).SOppSide x y
参数：x y : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.not_wOppSide_bot`：not_wOppSide_bot (x y : P) : ¬(⊥ : Affi
neSubspace R P).WOppSide x y
· 使用定理 `AffineSubspace.SOppSide.wOppSide`：∀ {R : Type u_1} {V : Type u_2} {P : T
ype u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrder
edRing R] [inst_3 : Ad…
-/
theorem not_sOppSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).SOppSide x y :=
  fun h => not_wOppSide_bot x y h.wOppSide

@[simp]
/-
**AffineSubspace.wSameSide_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：wSameSide_self_iff {s : AffineSubspace R P} {x : P} : s.WSameSide x x ↔ (s
 : Set P).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WSameSide.nonempty`：∀ {R : Type u_1} {V : Type u_2} {P : 
Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrde
redRing R] [inst_3 : Ad…
· 使用定理 `SameRay.rfl`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialO
rder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoi
d…
-/
theorem wSameSide_self_iff {s : AffineSubspace R P} {x : P} :
    s.WSameSide x x ↔ (s : Set P).Nonempty :=
  ⟨fun h => h.nonempty, fun ⟨p, hp⟩ => ⟨p, hp, p, hp, SameRay.rfl⟩⟩
/-
**AffineSubspace.sSameSide_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：sSameSide_self_iff {s : AffineSubspace R P} {x : P} : s.SSameSide x x ↔ (s
 : Set P).Nonempty ∧ x ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.wSameSide_self_iff`：wSameSide_self_iff {s : AffineSubspac
e R P} {x : P} : s.WSameSide x x ↔ (s : Set P).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem sSameSide_self_iff {s : AffineSubspace R P} {x : P} :
    s.SSameSide x x ↔ (s : Set P).Nonempty ∧ x ∉ s :=
  ⟨fun ⟨h, hx, _⟩ => ⟨wSameSide_self_iff.1 h, hx⟩, fun ⟨h, hx⟩ => ⟨wSameSide_self_iff.2 h, hx, hx⟩⟩
/-
**AffineSubspace.wSameSide_of_left_mem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
`。
形式化陈述：wSameSide_of_left_mem {s : AffineSubspace R P} {x : P} (y : P) (hx : x in 
s) : s.WSameSide x y
参数：y : P；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `SameRay.zero_left`：zero_left (y : M) : SameRay R 0 y
-/
theorem wSameSide_of_left_mem {s : AffineSubspace R P} {x : P} (y : P) (hx : x ∈ s) :
    s.WSameSide x y := by
  refine ⟨x, hx, x, hx, ?_⟩
  rw [vsub_self]
  apply SameRay.zero_left
/-
**AffineSubspace.wSameSide_of_right_mem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e`。
形式化陈述：wSameSide_of_right_mem {s : AffineSubspace R P} (x : P) {y : P} (hy : y in
 s) : s.WSameSide x y
参数：x : P；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WSameSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.wSameSide_of_left_mem`：wSameSide_of_left_mem {s : AffineS
ubspace R P} {x : P} (y : P) (hx : x in s) : s.WSameSide x y
-/
theorem wSameSide_of_right_mem {s : AffineSubspace R P} (x : P) {y : P} (hy : y ∈ s) :
    s.WSameSide x y :=
  (wSameSide_of_left_mem x hy).symm
/-
**AffineSubspace.wOppSide_of_left_mem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`
。
形式化陈述：wOppSide_of_left_mem {s : AffineSubspace R P} {x : P} (y : P) (hx : x in s
) : s.WOppSide x y
参数：y : P；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `SameRay.zero_left`：zero_left (y : M) : SameRay R 0 y
-/
theorem wOppSide_of_left_mem {s : AffineSubspace R P} {x : P} (y : P) (hx : x ∈ s) :
    s.WOppSide x y := by
  refine ⟨x, hx, x, hx, ?_⟩
  rw [vsub_self]
  apply SameRay.zero_left
/-
**AffineSubspace.wOppSide_of_right_mem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
`。
形式化陈述：wOppSide_of_right_mem {s : AffineSubspace R P} (x : P) {y : P} (hy : y in 
s) : s.WOppSide x y
参数：x : P；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.wOppSide_of_left_mem`：wOppSide_of_left_mem {s : AffineSub
space R P} {x : P} (y : P) (hx : x in s) : s.WOppSide x y
-/
theorem wOppSide_of_right_mem {s : AffineSubspace R P} (x : P) {y : P} (hy : y ∈ s) :
    s.WOppSide x y :=
  (wOppSide_of_left_mem x hy).symm
/-
**AffineSubspace.wSameSide_vadd_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspa
ce`。
形式化陈述：wSameSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v
 in s.direction) : s.WSameSide (v +ᵥ x) y ↔ s.WSameSide x y
参数：hv : v in s.direction。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `vadd_vsub_vadd_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddC
ommGroup G] [inst_1 : AddTorsor G P] (v : G) (p₁ p₂ : P),   (v +ᵥ p₁) -ᵥ (v +ᵥ p
₂) = p₁ -ᵥ p₂
-/
theorem wSameSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.WSameSide (v +ᵥ x) y ↔ s.WSameSide x y := by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine
      ⟨-v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) hp₁, p₂, hp₂, ?_⟩
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ← vadd_vsub_assoc]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction hv hp₁, p₂, hp₂, ?_⟩
    rwa [vadd_vsub_vadd_cancel_left]
/-
**AffineSubspace.wSameSide_vadd_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：wSameSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : 
v in s.direction) : s.WSameSide x (v +ᵥ y) ↔ s.WSameSide x y
参数：hv : v in s.direction。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.wSameSide_comm`：wSameSide_comm {s : AffineSubspace R P} {
x y : P} : s.WSameSide x y ↔ s.WSameSide y x
· 使用定理 `AffineSubspace.wSameSide_vadd_left_iff`：wSameSide_vadd_left_iff {s : Aff
ineSubspace R P} {x y : P} {v : V} (hv : v in s.direction) : s.WSameSide (v +ᵥ x
) y ↔ s.WSameSide x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem wSameSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.WSameSide x (v +ᵥ y) ↔ s.WSameSide x y := by
  rw [wSameSide_comm, wSameSide_vadd_left_iff hv, wSameSide_comm]
/-
**AffineSubspace.sSameSide_vadd_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspa
ce`。
形式化陈述：sSameSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v
 in s.direction) : s.SSameSide (v +ᵥ x) y ↔ s.SSameSide x y
参数：hv : v in s.direction。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.SSameSide.eq_1`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.wSameSide_vadd_left_iff`：wSameSide_vadd_left_iff {s : Aff
ineSubspace R P} {x y : P} {v : V} (hv : v in s.direction) : s.WSameSide (v +ᵥ x
) y ↔ s.WSameSide x y
· 使用定理 `AffineSubspace.vadd_mem_iff_mem_of_mem_direction`：vadd_mem_iff_mem_of_me
m_direction {s : AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} : v
 +ᵥ p in s ↔ p in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sSameSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.SSameSide (v +ᵥ x) y ↔ s.SSameSide x y := by
  rw [SSameSide, SSameSide, wSameSide_vadd_left_iff hv, vadd_mem_iff_mem_of_mem_direction hv]
/-
**AffineSubspace.sSameSide_vadd_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：sSameSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : 
v in s.direction) : s.SSameSide x (v +ᵥ y) ↔ s.SSameSide x y
参数：hv : v in s.direction。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.sSameSide_comm`：sSameSide_comm {s : AffineSubspace R P} {
x y : P} : s.SSameSide x y ↔ s.SSameSide y x
· 使用定理 `AffineSubspace.sSameSide_vadd_left_iff`：sSameSide_vadd_left_iff {s : Aff
ineSubspace R P} {x y : P} {v : V} (hv : v in s.direction) : s.SSameSide (v +ᵥ x
) y ↔ s.SSameSide x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sSameSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.SSameSide x (v +ᵥ y) ↔ s.SSameSide x y := by
  rw [sSameSide_comm, sSameSide_vadd_left_iff hv, sSameSide_comm]
/-
**AffineSubspace.wOppSide_vadd_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e`。
形式化陈述：wOppSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v 
in s.direction) : s.WOppSide (v +ᵥ x) y ↔ s.WOppSide x y
参数：hv : v in s.direction。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `vadd_vsub_vadd_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddC
ommGroup G] [inst_1 : AddTorsor G P] (v : G) (p₁ p₂ : P),   (v +ᵥ p₁) -ᵥ (v +ᵥ p
₂) = p₁ -ᵥ p₂
-/
theorem wOppSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.WOppSide (v +ᵥ x) y ↔ s.WOppSide x y := by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine
      ⟨-v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) hp₁, p₂, hp₂, ?_⟩
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ← vadd_vsub_assoc]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction hv hp₁, p₂, hp₂, ?_⟩
    rwa [vadd_vsub_vadd_cancel_left]
/-
**AffineSubspace.wOppSide_vadd_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspa
ce`。
形式化陈述：wOppSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v
 in s.direction) : s.WOppSide x (v +ᵥ y) ↔ s.WOppSide x y
参数：hv : v in s.direction。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.wOppSide_comm`：wOppSide_comm {s : AffineSubspace R P} {x 
y : P} : s.WOppSide x y ↔ s.WOppSide y x
· 使用定理 `AffineSubspace.wOppSide_vadd_left_iff`：wOppSide_vadd_left_iff {s : Affin
eSubspace R P} {x y : P} {v : V} (hv : v in s.direction) : s.WOppSide (v +ᵥ x) y
 ↔ s.WOppSide x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem wOppSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.WOppSide x (v +ᵥ y) ↔ s.WOppSide x y := by
  rw [wOppSide_comm, wOppSide_vadd_left_iff hv, wOppSide_comm]
/-
**AffineSubspace.sOppSide_vadd_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e`。
形式化陈述：sOppSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v 
in s.direction) : s.SOppSide (v +ᵥ x) y ↔ s.SOppSide x y
参数：hv : v in s.direction。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.SOppSide.eq_1`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.wOppSide_vadd_left_iff`：wOppSide_vadd_left_iff {s : Affin
eSubspace R P} {x y : P} {v : V} (hv : v in s.direction) : s.WOppSide (v +ᵥ x) y
 ↔ s.WOppSide x y
· 使用定理 `AffineSubspace.vadd_mem_iff_mem_of_mem_direction`：vadd_mem_iff_mem_of_me
m_direction {s : AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} : v
 +ᵥ p in s ↔ p in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sOppSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.SOppSide (v +ᵥ x) y ↔ s.SOppSide x y := by
  rw [SOppSide, SOppSide, wOppSide_vadd_left_iff hv, vadd_mem_iff_mem_of_mem_direction hv]
/-
**AffineSubspace.sOppSide_vadd_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspa
ce`。
形式化陈述：sOppSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v
 in s.direction) : s.SOppSide x (v +ᵥ y) ↔ s.SOppSide x y
参数：hv : v in s.direction。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.sOppSide_comm`：sOppSide_comm {s : AffineSubspace R P} {x 
y : P} : s.SOppSide x y ↔ s.SOppSide y x
· 使用定理 `AffineSubspace.sOppSide_vadd_left_iff`：sOppSide_vadd_left_iff {s : Affin
eSubspace R P} {x y : P} {v : V} (hv : v in s.direction) : s.SOppSide (v +ᵥ x) y
 ↔ s.SOppSide x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sOppSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.SOppSide x (v +ᵥ y) ↔ s.SOppSide x y := by
  rw [sOppSide_comm, sOppSide_vadd_left_iff hv, sOppSide_comm]
/-
**AffineSubspace.wSameSide_smul_vsub_vadd_left** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Subspace`。
形式化陈述：wSameSide_smul_vsub_vadd_left {s : AffineSubspace R P} {p₁ p₂ : P} (x : P)
 (hp₁ : p₁ in s) (hp₂ : p₂ in s) {t : R} (ht : 0 <= t) : s.WSameSide (t • (x -ᵥ 
p₁) +ᵥ p₂) x
参数：x : P；hp₁ : p₁ in s；hp₂ : p₂ in s；ht : 0 <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用引理 `SameRay.sameRay_nonneg_smul_left`：sameRay_nonneg_smul_left (v : M) (ha :
 0 <= a) : SameRay R (a • v) v
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
theorem wSameSide_smul_vsub_vadd_left {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : 0 ≤ t) : s.WSameSide (t • (x -ᵥ p₁) +ᵥ p₂) x := by
  refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
  rw [vadd_vsub]
  exact SameRay.sameRay_nonneg_smul_left _ ht
/-
**AffineSubspace.wSameSide_smul_vsub_vadd_right** 是 Mathlib 中的一个定理，位于命名空间 `Affin
eSubspace`。
形式化陈述：wSameSide_smul_vsub_vadd_right {s : AffineSubspace R P} {p₁ p₂ : P} (x : P
) (hp₁ : p₁ in s) (hp₂ : p₂ in s) {t : R} (ht : 0 <= t) : s.WSameSide x (t • (x 
-ᵥ p₁) +ᵥ p₂)
参数：x : P；hp₁ : p₁ in s；hp₂ : p₂ in s；ht : 0 <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WSameSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.wSameSide_smul_vsub_vadd_left`：wSameSide_smul_vsub_vadd_l
eft {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s) (hp₂ : p₂ in s)
 {t : R} (ht : 0 <= t) : s.WSameSi…
-/
theorem wSameSide_smul_vsub_vadd_right {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : 0 ≤ t) : s.WSameSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (wSameSide_smul_vsub_vadd_left x hp₁ hp₂ ht).symm

set_option backward.isDefEq.respectTransparency false in
/-
**AffineSubspace.wSameSide_lineMap_left** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e`。
形式化陈述：wSameSide_lineMap_left {s : AffineSubspace R P} {x : P} (y : P) (h : x in 
s) {t : R} (ht : 0 <= t) : s.WSameSide (lineMap x y t) y
参数：y : P；h : x in s；ht : 0 <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.wSameSide_smul_vsub_vadd_left`：wSameSide_smul_vsub_vadd_l
eft {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s) (hp₂ : p₂ in s)
 {t : R} (ht : 0 <= t) : s.WSameSi…
-/
theorem wSameSide_lineMap_left {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : 0 ≤ t) : s.WSameSide (lineMap x y t) y :=
  wSameSide_smul_vsub_vadd_left y h h ht

set_option backward.isDefEq.respectTransparency false in
/-
**AffineSubspace.wSameSide_lineMap_right** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspa
ce`。
形式化陈述：wSameSide_lineMap_right {s : AffineSubspace R P} {x : P} (y : P) (h : x in
 s) {t : R} (ht : 0 <= t) : s.WSameSide y (lineMap x y t)
参数：y : P；h : x in s；ht : 0 <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WSameSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.wSameSide_lineMap_left`：wSameSide_lineMap_left {s : Affin
eSubspace R P} {x : P} (y : P) (h : x in s) {t : R} (ht : 0 <= t) : s.WSameSide 
(lineMap x y t) y
-/
theorem wSameSide_lineMap_right {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : 0 ≤ t) : s.WSameSide y (lineMap x y t) :=
  (wSameSide_lineMap_left y h ht).symm
/-
**AffineSubspace.wOppSide_smul_vsub_vadd_left** 是 Mathlib 中的一个定理，位于命名空间 `AffineS
ubspace`。
形式化陈述：wOppSide_smul_vsub_vadd_left {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) 
(hp₁ : p₁ in s) (hp₂ : p₂ in s) {t : R} (ht : t <= 0) : s.WOppSide (t • (x -ᵥ p₁
) +ᵥ p₂) x
参数：x : P；hp₁ : p₁ in s；hp₂ : p₂ in s；ht : t <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用引理 `SameRay.sameRay_nonneg_smul_left`：sameRay_nonneg_smul_left (v : M) (ha :
 0 <= a) : SameRay R (a • v) v
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem wOppSide_smul_vsub_vadd_left {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : t ≤ 0) : s.WOppSide (t • (x -ᵥ p₁) +ᵥ p₂) x := by
  refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
  rw [vadd_vsub, ← neg_neg t, neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]
  exact SameRay.sameRay_nonneg_smul_left _ (neg_nonneg.2 ht)
/-
**AffineSubspace.wOppSide_smul_vsub_vadd_right** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Subspace`。
形式化陈述：wOppSide_smul_vsub_vadd_right {s : AffineSubspace R P} {p₁ p₂ : P} (x : P)
 (hp₁ : p₁ in s) (hp₂ : p₂ in s) {t : R} (ht : t <= 0) : s.WOppSide x (t • (x -ᵥ
 p₁) +ᵥ p₂)
参数：x : P；hp₁ : p₁ in s；hp₂ : p₂ in s；ht : t <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.wOppSide_smul_vsub_vadd_left`：wOppSide_smul_vsub_vadd_lef
t {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s) (hp₂ : p₂ in s) {
t : R} (ht : t <= 0) : s.WOppSide…
-/
theorem wOppSide_smul_vsub_vadd_right {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : t ≤ 0) : s.WOppSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (wOppSide_smul_vsub_vadd_left x hp₁ hp₂ ht).symm

set_option backward.isDefEq.respectTransparency false in
/-
**AffineSubspace.wOppSide_lineMap_left** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
`。
形式化陈述：wOppSide_lineMap_left {s : AffineSubspace R P} {x : P} (y : P) (h : x in s
) {t : R} (ht : t <= 0) : s.WOppSide (lineMap x y t) y
参数：y : P；h : x in s；ht : t <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.wOppSide_smul_vsub_vadd_left`：wOppSide_smul_vsub_vadd_lef
t {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s) (hp₂ : p₂ in s) {
t : R} (ht : t <= 0) : s.WOppSide…
-/
theorem wOppSide_lineMap_left {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : t ≤ 0) : s.WOppSide (lineMap x y t) y :=
  wOppSide_smul_vsub_vadd_left y h h ht

set_option backward.isDefEq.respectTransparency false in
/-
**AffineSubspace.wOppSide_lineMap_right** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e`。
形式化陈述：wOppSide_lineMap_right {s : AffineSubspace R P} {x : P} (y : P) (h : x in 
s) {t : R} (ht : t <= 0) : s.WOppSide y (lineMap x y t)
参数：y : P；h : x in s；ht : t <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.wOppSide_lineMap_left`：wOppSide_lineMap_left {s : AffineS
ubspace R P} {x : P} (y : P) (h : x in s) {t : R} (ht : t <= 0) : s.WOppSide (li
neMap x y t) y
-/
theorem wOppSide_lineMap_right {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : t ≤ 0) : s.WOppSide y (lineMap x y t) :=
  (wOppSide_lineMap_left y h ht).symm
/-
**AffineSubspace._root_.Wbtw.wSameSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Wbtw.wSameSide₂₃ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hx : x ∈ s) : s.WSameSide y z := by
  rcases h with ⟨t, ⟨ht0, -⟩, rfl⟩
  exact wSameSide_lineMap_left z hx ht0
/-
**AffineSubspace._root_.Wbtw.wSameSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Wbtw.wSameSide₃₂ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hx : x ∈ s) : s.WSameSide z y :=
  (h.wSameSide₂₃ hx).symm
/-
**AffineSubspace._root_.Wbtw.wSameSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Wbtw.wSameSide₁₂ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hz : z ∈ s) : s.WSameSide x y :=
  h.symm.wSameSide₃₂ hz
/-
**AffineSubspace._root_.Wbtw.wSameSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Wbtw.wSameSide₂₁ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hz : z ∈ s) : s.WSameSide y x :=
  h.symm.wSameSide₂₃ hz
/-
**AffineSubspace._root_.Wbtw.wOppSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Wbtw.wOppSide₁₃ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hy : y ∈ s) : s.WOppSide x z := by
  rcases h with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  refine ⟨_, hy, _, hy, ?_⟩
  rcases ht1.lt_or_eq with (ht1' | rfl); swap
  · simp
  rcases ht0.lt_or_eq with (ht0' | rfl); swap
  · simp
  refine Or.inr (Or.inr ⟨1 - t, t, sub_pos.2 ht1', ht0', ?_⟩)
  rw [lineMap_apply, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, ← neg_vsub_eq_vsub_rev z, vsub_self]
  module
/-
**AffineSubspace._root_.Wbtw.wOppSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Wbtw.wOppSide₃₁ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hy : y ∈ s) : s.WOppSide z x :=
  h.symm.wOppSide₁₃ hy

end StrictOrderedCommRing

section LinearOrderedCommRing

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- If `x` and `y` are displaced from points of `s` by multiples of a common vector whose
coefficients have nonnegative product, they are weakly on the same side of `s`. -/
/-
**AffineSubspace.wSameSide_of_vsub_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
形式化陈述：wSameSide_of_vsub_eq_smul {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V}
 {c₁ c₂ : R} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ 
p₂ = c₂ • m) (hc : 0 <= c₁ * c₂) : s.WSameSide x y
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；h₁ : x -ᵥ p₁ = c₁ • m；h₂ : y -ᵥ p₂ = c₂ • m；hc : 
0 <= c₁ * c₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sameRay_smul_smul_of_mul_nonneg`：sameRay_smul_smul_of_mul_nonneg {v : M}
 {c₁ c₂ : R} (h : 0 <= c₁ * c₂) : SameRay R (c₁ • v) (c₂ • v)

--- 原说明 ---
If `x` and `y` are displaced from points of `s` by multiples of a common vector 
whose
coefficients have nonnegative product, they are weakly on the same side of `s`.
-/
theorem wSameSide_of_vsub_eq_smul {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ p₂ = c₂ • m)
    (hc : 0 ≤ c₁ * c₂) : s.WSameSide x y := by
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  rw [h₁, h₂]
  exact sameRay_smul_smul_of_mul_nonneg hc

/-- If `x` and `y` are displaced from points of `s` by multiples of a common vector whose
coefficients have nonpositive product, they are weakly on opposite sides of `s`. -/
/-
**AffineSubspace.wOppSide_of_vsub_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：wOppSide_of_vsub_eq_smul {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} 
{c₁ c₂ : R} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ p
₂ = c₂ • m) (hc : c₁ * c₂ <= 0) : s.WOppSide x y
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；h₁ : x -ᵥ p₁ = c₁ • m；h₂ : y -ᵥ p₂ = c₂ • m；hc : 
c₁ * c₂ <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `sameRay_smul_smul_of_mul_nonneg`：sameRay_smul_smul_of_mul_nonneg {v : M}
 {c₁ c₂ : R} (h : 0 <= c₁ * c₂) : SameRay R (c₁ • v) (c₂ • v)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R

--- 原说明 ---
If `x` and `y` are displaced from points of `s` by multiples of a common vector 
whose
coefficients have nonpositive product, they are weakly on opposite sides of `s`.
-/
theorem wOppSide_of_vsub_eq_smul {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ p₂ = c₂ • m)
    (hc : c₁ * c₂ ≤ 0) : s.WOppSide x y := by
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  have h₂' : p₂ -ᵥ y = (-c₂) • m := by rw [← neg_vsub_eq_vsub_rev, h₂, neg_smul]
  rw [h₁, h₂']
  exact sameRay_smul_smul_of_mul_nonneg (by rw [mul_neg]; exact neg_nonneg.2 hc)

/-- If `x` and `y` lie off `s` and are displaced from points of `s` by multiples of a common
vector whose coefficients have nonnegative product, they are strictly on the same side of `s`. -/
/-
**AffineSubspace.sSameSide_of_vsub_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
形式化陈述：sSameSide_of_vsub_eq_smul {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V}
 {c₁ c₂ : R} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ 
p₂ = c₂ • m) (hc : 0 <= c₁ * c₂) (hx : x ∉ s) (hy : y ∉ s) : s.SSameSide x y
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；h₁ : x -ᵥ p₁ = c₁ • m；h₂ : y -ᵥ p₂ = c₂ • m；hc : 
0 <= c₁ * c₂；hx : x ∉ s；hy : y ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.wSameSide_of_vsub_eq_smul`：wSameSide_of_vsub_eq_smul {s :
 AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R} (hp₁ : p₁ in s) (hp₂ : 
p₂ in s) (h₁ : x -ᵥ p₁ = c₁ • …

--- 原说明 ---
If `x` and `y` lie off `s` and are displaced from points of `s` by multiples of 
a common
vector whose coefficients have nonnegative product, they are strictly on the sam
e side of `s`.
-/
theorem sSameSide_of_vsub_eq_smul {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ p₂ = c₂ • m)
    (hc : 0 ≤ c₁ * c₂) (hx : x ∉ s) (hy : y ∉ s) : s.SSameSide x y :=
  ⟨wSameSide_of_vsub_eq_smul hp₁ hp₂ h₁ h₂ hc, hx, hy⟩

/-- If `x` and `y` lie off `s` and are displaced from points of `s` by multiples of a common
vector whose coefficients have nonpositive product, they are strictly on opposite sides of `s`. -/
/-
**AffineSubspace.sOppSide_of_vsub_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：sOppSide_of_vsub_eq_smul {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} 
{c₁ c₂ : R} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ p
₂ = c₂ • m) (hc : c₁ * c₂ <= 0) (hx : x ∉ s) (hy : y ∉ s) : s.SOppSide x y
参数：hp₁ : p₁ in s；hp₂ : p₂ in s；h₁ : x -ᵥ p₁ = c₁ • m；h₂ : y -ᵥ p₂ = c₂ • m；hc : 
c₁ * c₂ <= 0；hx : x ∉ s；hy : y ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.wOppSide_of_vsub_eq_smul`：wOppSide_of_vsub_eq_smul {s : A
ffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R} (hp₁ : p₁ in s) (hp₂ : p₂
 in s) (h₁ : x -ᵥ p₁ = c₁ • m…

--- 原说明 ---
If `x` and `y` lie off `s` and are displaced from points of `s` by multiples of 
a common
vector whose coefficients have nonpositive product, they are strictly on opposit
e sides of `s`.
-/
theorem sOppSide_of_vsub_eq_smul {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ p₂ = c₂ • m)
    (hc : c₁ * c₂ ≤ 0) (hx : x ∉ s) (hy : y ∉ s) : s.SOppSide x y :=
  ⟨wOppSide_of_vsub_eq_smul hp₁ hp₂ h₁ h₂ hc, hx, hy⟩

end LinearOrderedCommRing

section LinearOrderedField

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]

@[simp]
/-
**AffineSubspace.wOppSide_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：wOppSide_self_iff {s : AffineSubspace R P} {x : P} : s.WOppSide x x ↔ x in
 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.exists_eq_smul_add`：exists_eq_smul_add (h : SameRay R v₁ v₂) : e
xists a b : R, 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ v₁ = a • (v₁ + v₂) ∧ v₂ = b • (v₁ +
 v₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_vadd_iff_vsub_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p₁ : P) (g : G) (p₂ : P),   p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `AffineSubspace.smul_vsub_vadd_mem`：smul_vsub_vadd_mem (s : AffineSubspac
e k P) (c : k) {p₁ p₂ p₃ : P} : p₁ in s -> p₂ in s -> p₃ in s -> c • (p₁ -ᵥ p₂ :
 V) +ᵥ p₃ in s
· 使用定理 `SameRay.rfl`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialO
rder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoi
d…
-/
theorem wOppSide_self_iff {s : AffineSubspace R P} {x : P} : s.WOppSide x x ↔ x ∈ s := by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    obtain ⟨a, -, -, -, -, h₁, -⟩ := h.exists_eq_smul_add
    rw [add_comm, vsub_add_vsub_cancel, ← eq_vadd_iff_vsub_eq] at h₁
    rw [h₁]
    exact s.smul_vsub_vadd_mem a hp₂ hp₁ hp₁
  · exact fun h => ⟨x, h, x, h, SameRay.rfl⟩
/-
**AffineSubspace.not_sOppSide_self** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：not_sOppSide_self (s : AffineSubspace R P) (x : P) : ¬s.SOppSide x x
参数：s : AffineSubspace R P；x : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.SOppSide.eq_1`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_sOppSide_self (s : AffineSubspace R P) (x : P) : ¬s.SOppSide x x := by
  rw [SOppSide]
  simp
/-
**AffineSubspace.wSameSide_iff_exists_left** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
形式化陈述：wSameSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in
 s) : s.WSameSide x y ↔ x in s ∨ exists p₂ in s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂)
参数：h : p₁ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `SameRay.zero_right`：zero_right (x : M) : SameRay R x 0
· 使用引理 `AffineSubspace.smul_vsub_vadd_mem`：smul_vsub_vadd_mem (s : AffineSubspac
e k P) (c : k) {p₁ p₂ p₃ : P} : p₁ in s -> p₂ in s -> p₃ in s -> c • (p₁ -ᵥ p₂ :
 V) +ᵥ p₃ in s
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `AffineSubspace.wSameSide_of_left_mem`：wSameSide_of_left_mem {s : AffineS
ubspace R P} {x : P} (y : P) (hx : x in s) : s.WSameSide x y
-/
theorem wSameSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.WSameSide x y ↔ x ∈ s ∨ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) := by
  constructor
  · rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h0
      rw [h0]
      exact Or.inl hp₁'
    · refine Or.inr ⟨p₂', hp₂', ?_⟩
      rw [h0]
      exact SameRay.zero_right _
    · refine Or.inr ⟨(r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.smul_vsub_vadd_mem _ h hp₁' hp₂',
        Or.inr (Or.inr ⟨r₁, r₂, hr₁, hr₂, ?_⟩)⟩
      rw [vsub_vadd_eq_vsub_sub, smul_sub, ← hr, smul_smul, mul_div_cancel₀ _ hr₂.ne.symm,
        ← smul_sub, vsub_sub_vsub_cancel_right]
  · rintro (h' | ⟨h₁, h₂, h₃⟩)
    · exact wSameSide_of_left_mem y h'
    · exact ⟨p₁, h, h₁, h₂, h₃⟩
/-
**AffineSubspace.wSameSide_iff_exists_right** 是 Mathlib 中的一个定理，位于命名空间 `AffineSub
space`。
形式化陈述：wSameSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ i
n s) : s.WSameSide x y ↔ y in s ∨ exists p₁ in s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂)
参数：h : p₂ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.wSameSide_comm`：wSameSide_comm {s : AffineSubspace R P} {
x y : P} : s.WSameSide x y ↔ s.WSameSide y x
· 使用定理 `AffineSubspace.wSameSide_iff_exists_left`：wSameSide_iff_exists_left {s :
 AffineSubspace R P} {x y p₁ : P} (h : p₁ in s) : s.WSameSide x y ↔ x in s ∨ exi
sts p₂ in s, SameRay R (x -ᵥ p…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem wSameSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.WSameSide x y ↔ y ∈ s ∨ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) := by
  rw [wSameSide_comm, wSameSide_iff_exists_left h]
  simp_rw [SameRay.sameRay_comm]
/-
**AffineSubspace.sSameSide_iff_exists_left** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
形式化陈述：sSameSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in
 s) : s.SSameSide x y ↔ x ∉ s ∧ y ∉ s ∧ exists p₂ in s, SameRay R (x -ᵥ p₁) (y -
ᵥ p₂)
参数：h : p₁ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.SSameSide.eq_1`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `AffineSubspace.wSameSide_iff_exists_left`：wSameSide_iff_exists_left {s :
 AffineSubspace R P} {x y p₁ : P} (h : p₁ in s) : s.WSameSide x y ↔ x in s ∨ exi
sts p₂ in s, SameRay R (x -ᵥ p…
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sSameSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.SSameSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) := by
  rw [SSameSide, and_comm, wSameSide_iff_exists_left h, and_assoc, and_congr_right_iff]
  intro hx
  rw [or_iff_right hx]
/-
**AffineSubspace.sSameSide_iff_exists_right** 是 Mathlib 中的一个定理，位于命名空间 `AffineSub
space`。
形式化陈述：sSameSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ i
n s) : s.SSameSide x y ↔ x ∉ s ∧ y ∉ s ∧ exists p₁ in s, SameRay R (x -ᵥ p₁) (y 
-ᵥ p₂)
参数：h : p₂ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.sSameSide_comm`：sSameSide_comm {s : AffineSubspace R P} {
x y : P} : s.SSameSide x y ↔ s.SSameSide y x
· 使用定理 `AffineSubspace.sSameSide_iff_exists_left`：sSameSide_iff_exists_left {s :
 AffineSubspace R P} {x y p₁ : P} (h : p₁ in s) : s.SSameSide x y ↔ x ∉ s ∧ y ∉ 
s ∧ exists p₂ in s, SameRay R …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sSameSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.SSameSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) := by
  rw [sSameSide_comm, sSameSide_iff_exists_left h, ← and_assoc, and_comm (a := y ∉ s), and_assoc]
  simp_rw [SameRay.sameRay_comm]
/-
**AffineSubspace.wOppSide_iff_exists_left** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：wOppSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in 
s) : s.WOppSide x y ↔ x in s ∨ exists p₂ in s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)
参数：h : p₁ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `SameRay.zero_right`：zero_right (x : M) : SameRay R x 0
· 使用引理 `AffineSubspace.smul_vsub_vadd_mem`：smul_vsub_vadd_mem (s : AffineSubspac
e k P) (c : k) {p₁ p₂ p₃ : P} : p₁ in s -> p₂ in s -> p₃ in s -> c • (p₁ -ᵥ p₂ :
 V) +ᵥ p₃ in s
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₁`：sub_eq_eval₁ [SMul R M] [AddGroup
 M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval - (a₂ ::ᵣ l₂).eval
 = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₃`：add_eq_eval₃ [Semiring R] [AddCom
mMonoid M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::
ᵣ l₁).eval + l₂.eval = l.ev…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₂`：sub_eq_eval₂ [Ring R] [AddCommGro
up M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval - l₂.eval
 = l.eval) : ((r₁, x) ::ᵣ l…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_eq_eval`：zero_eq_eval [AddMonoid M] : (0:M
) = NF.eval (R
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_const`：eq_cons_const [AddCommMonoid M] 
[Semiring R] [Module R M] {r : R} (m : M) {n : M} {l : NF R M} (h1 : r = 0) (h2 
: l.eval = n) : ((r, m) ::ᵣ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 91 条，此处仅展示前 30 条）
-/
theorem wOppSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.WOppSide x y ↔ x ∈ s ∨ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) := by
  constructor
  · rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h0
      rw [h0]
      exact Or.inl hp₁'
    · refine Or.inr ⟨p₂', hp₂', ?_⟩
      rw [h0]
      exact SameRay.zero_right _
    · refine Or.inr ⟨(-r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.smul_vsub_vadd_mem _ h hp₁' hp₂',
        Or.inr (Or.inr ⟨r₁, r₂, hr₁, hr₂, ?_⟩)⟩
      rw [vadd_vsub_assoc, ← vsub_sub_vsub_cancel_right x p₁ p₁']
      linear_combination (norm := match_scalars <;> field) hr
  · rintro (h' | ⟨h₁, h₂, h₃⟩)
    · exact wOppSide_of_left_mem y h'
    · exact ⟨p₁, h, h₁, h₂, h₃⟩
/-
**AffineSubspace.wOppSide_iff_exists_right** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
形式化陈述：wOppSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ in
 s) : s.WOppSide x y ↔ y in s ∨ exists p₁ in s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)
参数：h : p₂ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.wOppSide_comm`：wOppSide_comm {s : AffineSubspace R P} {x 
y : P} : s.WOppSide x y ↔ s.WOppSide y x
· 使用定理 `AffineSubspace.wOppSide_iff_exists_left`：wOppSide_iff_exists_left {s : A
ffineSubspace R P} {x y p₁ : P} (h : p₁ in s) : s.WOppSide x y ↔ x in s ∨ exists
 p₂ in s, SameRay R (x -ᵥ p₁)…
· 使用定理 `SameRay.sameRay_comm`：sameRay_comm : SameRay R x y ↔ SameRay R y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sameRay_neg_iff`：sameRay_neg_iff : SameRay R (-x) (-y) ↔ SameRay R x y
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
-/
theorem wOppSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.WOppSide x y ↔ y ∈ s ∨ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) := by
  rw [wOppSide_comm, wOppSide_iff_exists_left h]
  constructor
  · rintro (hy | ⟨p, hp, hr⟩)
    · exact Or.inl hy
    refine Or.inr ⟨p, hp, ?_⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  · rintro (hy | ⟨p, hp, hr⟩)
    · exact Or.inl hy
    refine Or.inr ⟨p, hp, ?_⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
/-
**AffineSubspace.sOppSide_iff_exists_left** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：sOppSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in 
s) : s.SOppSide x y ↔ x ∉ s ∧ y ∉ s ∧ exists p₂ in s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ
 y)
参数：h : p₁ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.SOppSide.eq_1`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `AffineSubspace.wOppSide_iff_exists_left`：wOppSide_iff_exists_left {s : A
ffineSubspace R P} {x y p₁ : P} (h : p₁ in s) : s.WOppSide x y ↔ x in s ∨ exists
 p₂ in s, SameRay R (x -ᵥ p₁)…
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sOppSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.SOppSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) := by
  rw [SOppSide, and_comm, wOppSide_iff_exists_left h, and_assoc, and_congr_right_iff]
  intro hx
  rw [or_iff_right hx]
/-
**AffineSubspace.sOppSide_iff_exists_right** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
形式化陈述：sOppSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ in
 s) : s.SOppSide x y ↔ x ∉ s ∧ y ∉ s ∧ exists p₁ in s, SameRay R (x -ᵥ p₁) (p₂ -
ᵥ y)
参数：h : p₂ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.SOppSide.eq_1`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `AffineSubspace.wOppSide_iff_exists_right`：wOppSide_iff_exists_right {s :
 AffineSubspace R P} {x y p₂ : P} (h : p₂ in s) : s.WOppSide x y ↔ y in s ∨ exis
ts p₁ in s, SameRay R (x -ᵥ p₁…
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sOppSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.SOppSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) := by
  rw [SOppSide, and_comm, wOppSide_iff_exists_right h, and_assoc, and_congr_right_iff,
    and_congr_right_iff]
  rintro _ hy
  rw [or_iff_right hy]
/-
**AffineSubspace.WSameSide.trans** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.WSame
Side`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.WSameSide x y → s.WSameSide y z → y ∉ s → s.WSameSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `AffineSubspace.wSameSide_iff_exists_left`：wSameSide_iff_exists_left {s :
 AffineSubspace R P} {x y p₁ : P} (h : p₁ in s) : s.WSameSide x y ↔ x in s ∨ exi
sts p₂ in s, SameRay R (x -ᵥ p…
· 使用定理 `SameRay.trans`：trans (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y
 = 0 -> x = 0 ∨ z = 0) : SameRay R x z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
-/
theorem WSameSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.WSameSide y z) (hy : y ∉ s) : s.WSameSide x z := by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [wSameSide_iff_exists_left hp₂, or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz ?_⟩
  refine fun h => False.elim ?_
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h.symm ▸ hp₂)
/-
**AffineSubspace.WSameSide.trans_sSameSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace.WSameSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.WSameSide x y → s.SSameSide y z → s.WSameSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WSameSide.trans`：∀ {R : Type u_1} {V : Type u_2} {P : Typ
e u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrderedRing
 R] [inst_3 : AddCom…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem WSameSide.trans_sSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.SSameSide y z) : s.WSameSide x z :=
  hxy.trans hyz.1 hyz.2.1
/-
**AffineSubspace.WSameSide.trans_wOppSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace.WSameSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.WSameSide x y → s.WOppSide y z → y ∉ s → s.WOppSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `AffineSubspace.wOppSide_iff_exists_left`：wOppSide_iff_exists_left {s : A
ffineSubspace R P} {x y p₁ : P} (h : p₁ in s) : s.WOppSide x y ↔ x in s ∨ exists
 p₂ in s, SameRay R (x -ᵥ p₁)…
· 使用定理 `SameRay.trans`：trans (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y
 = 0 -> x = 0 ∨ z = 0) : SameRay R x z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
-/
theorem WSameSide.trans_wOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.WOppSide y z) (hy : y ∉ s) : s.WOppSide x z := by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [wOppSide_iff_exists_left hp₂, or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz ?_⟩
  refine fun h => False.elim ?_
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h.symm ▸ hp₂)
/-
**AffineSubspace.WSameSide.trans_sOppSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace.WSameSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.WSameSide x y → s.SOppSide y z → s.WOppSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WSameSide.trans_wOppSide`：∀ {R : Type u_1} {V : Type u_2}
 {P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOr
deredRing R] [inst_3 : AddCom…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem WSameSide.trans_sOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.SOppSide y z) : s.WOppSide x z :=
  hxy.trans_wOppSide hyz.1 hyz.2.1
/-
**AffineSubspace.SSameSide.trans_wSameSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace.SSameSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.SSameSide x y → s.WSameSide y z → s.WSameSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WSameSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.WSameSide.trans_sSameSide`：∀ {R : Type u_1} {V : Type u_2
} {P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictO
rderedRing R] [inst_3 : AddCom…
· 使用定理 `AffineSubspace.SSameSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
-/
theorem SSameSide.trans_wSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.WSameSide y z) : s.WSameSide x z :=
  (hyz.symm.trans_sSameSide hxy.symm).symm
/-
**AffineSubspace.SSameSide.trans** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.SSame
Side`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.SSameSide x y → s.SSameSide y z → s.SSameSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WSameSide.trans_sSameSide`：∀ {R : Type u_1} {V : Type u_2
} {P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictO
rderedRing R] [inst_3 : AddCom…
· 使用定理 `AffineSubspace.SSameSide.wSameSide`：∀ {R : Type u_1} {V : Type u_2} {P :
 Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrd
eredRing R] [inst_3 : Ad…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem SSameSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.SSameSide y z) : s.SSameSide x z :=
  ⟨hxy.wSameSide.trans_sSameSide hyz, hxy.2.1, hyz.2.2⟩
/-
**AffineSubspace.SSameSide.trans_wOppSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace.SSameSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.SSameSide x y → s.WOppSide y z → s.WOppSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WSameSide.trans_wOppSide`：∀ {R : Type u_1} {V : Type u_2}
 {P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOr
deredRing R] [inst_3 : AddCom…
· 使用定理 `AffineSubspace.SSameSide.wSameSide`：∀ {R : Type u_1} {V : Type u_2} {P :
 Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrd
eredRing R] [inst_3 : Ad…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem SSameSide.trans_wOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.WOppSide y z) : s.WOppSide x z :=
  hxy.wSameSide.trans_wOppSide hyz hxy.2.2
/-
**AffineSubspace.SSameSide.trans_sOppSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace.SSameSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.SSameSide x y → s.SOppSide y z → s.SOppSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.SSameSide.trans_wOppSide`：∀ {R : Type u_1} {V : Type u_2}
 {P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOr
deredRing R] [inst_3 : AddCom…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem SSameSide.trans_sOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.SOppSide y z) : s.SOppSide x z :=
  ⟨hxy.trans_wOppSide hyz.1, hxy.2.1, hyz.2.2⟩
/-
**AffineSubspace.WOppSide.trans_wSameSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace.WOppSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.WOppSide x y → s.WSameSide y z → y ∉ s → s.WOppSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.WSameSide.trans_wOppSide`：∀ {R : Type u_1} {V : Type u_2}
 {P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOr
deredRing R] [inst_3 : AddCom…
· 使用定理 `AffineSubspace.WSameSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
-/
theorem WOppSide.trans_wSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.WSameSide y z) (hy : y ∉ s) : s.WOppSide x z :=
  (hyz.symm.trans_wOppSide hxy.symm hy).symm
/-
**AffineSubspace.WOppSide.trans_sSameSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace.WOppSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.WOppSide x y → s.SSameSide y z → s.WOppSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WOppSide.trans_wSameSide`：∀ {R : Type u_1} {V : Type u_2}
 {P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOr
deredRing R] [inst_3 : AddCom…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem WOppSide.trans_sSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.SSameSide y z) : s.WOppSide x z :=
  hxy.trans_wSameSide hyz.1 hyz.2.1
/-
**AffineSubspace.WOppSide.trans** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.WOppSi
de`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.WOppSide x y → s.WOppSide y z → y ∉ s → s.WSameSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `AffineSubspace.wOppSide_iff_exists_left`：wOppSide_iff_exists_left {s : A
ffineSubspace R P} {x y p₁ : P} (h : p₁ in s) : s.WOppSide x y ↔ x in s ∨ exists
 p₂ in s, SameRay R (x -ᵥ p₁)…
· 使用定理 `SameRay.trans`：trans (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y
 = 0 -> x = 0 ∨ z = 0) : SameRay R x z
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sameRay_neg_iff`：sameRay_neg_iff : SameRay R (-x) (-y) ↔ SameRay R x y
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
-/
theorem WOppSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.WOppSide y z) (hy : y ∉ s) : s.WSameSide x z := by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [wOppSide_iff_exists_left hp₂, or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  rw [← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hyz
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz ?_⟩
  refine fun h => False.elim ?_
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h ▸ hp₂)
/-
**AffineSubspace.WOppSide.trans_sOppSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspa
ce.WOppSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.WOppSide x y → s.SOppSide y z → s.WSameSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WOppSide.trans`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrderedRing 
R] [inst_3 : AddCom…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem WOppSide.trans_sOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.SOppSide y z) : s.WSameSide x z :=
  hxy.trans hyz.1 hyz.2.1
/-
**AffineSubspace.SOppSide.trans_wSameSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace.SOppSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.SOppSide x y → s.WSameSide y z → s.WOppSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.WSameSide.trans_sOppSide`：∀ {R : Type u_1} {V : Type u_2}
 {P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOr
deredRing R] [inst_3 : AddCom…
· 使用定理 `AffineSubspace.WSameSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.SOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
-/
theorem SOppSide.trans_wSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.WSameSide y z) : s.WOppSide x z :=
  (hyz.symm.trans_sOppSide hxy.symm).symm
/-
**AffineSubspace.SOppSide.trans_sSameSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace.SOppSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.SOppSide x y → s.SSameSide y z → s.SOppSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.SOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.SSameSide.trans_sOppSide`：∀ {R : Type u_1} {V : Type u_2}
 {P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOr
deredRing R] [inst_3 : AddCom…
· 使用定理 `AffineSubspace.SSameSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
-/
theorem SOppSide.trans_sSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.SSameSide y z) : s.SOppSide x z :=
  (hyz.symm.trans_sOppSide hxy.symm).symm
/-
**AffineSubspace.SOppSide.trans_wOppSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspa
ce.SOppSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.SOppSide x y → s.WOppSide y z → s.WSameSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WSameSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.WOppSide.trans_sOppSide`：∀ {R : Type u_1} {V : Type u_2} 
{P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrd
eredRing R] [inst_3 : AddCom…
· 使用定理 `AffineSubspace.WOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.SOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
-/
theorem SOppSide.trans_wOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.WOppSide y z) : s.WSameSide x z :=
  (hyz.symm.trans_sOppSide hxy.symm).symm
/-
**AffineSubspace.SOppSide.trans** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.SOppSi
de`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y z : P}, s.SOppSide x y → s.SOppSide y z → s.SSameSide x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.SOppSide.trans_wOppSide`：∀ {R : Type u_1} {V : Type u_2} 
{P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrd
eredRing R] [inst_3 : AddCom…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem SOppSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.SOppSide y z) : s.SSameSide x z :=
  ⟨hxy.trans_wOppSide hyz.1, hxy.2.1, hyz.2.2⟩
/-
**AffineSubspace.wSameSide_and_wOppSide_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSub
space`。
形式化陈述：wSameSide_and_wOppSide_iff {s : AffineSubspace R P} {x y : P} : s.WSameSid
e x y ∧ s.WOppSide x y ↔ x in s ∨ y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.wOppSide_self_iff`：wOppSide_self_iff {s : AffineSubspace 
R P} {x : P} : s.WOppSide x x ↔ x in s
· 使用定理 `AffineSubspace.WSameSide.trans_wOppSide`：∀ {R : Type u_1} {V : Type u_2}
 {P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOr
deredRing R] [inst_3 : AddCom…
· 使用定理 `AffineSubspace.wOppSide_comm`：wOppSide_comm {s : AffineSubspace R P} {x 
y : P} : s.WOppSide x y ↔ s.WOppSide y x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AffineSubspace.wSameSide_of_left_mem`：wSameSide_of_left_mem {s : AffineS
ubspace R P} {x : P} (y : P) (hx : x in s) : s.WSameSide x y
· 使用定理 `AffineSubspace.wOppSide_of_left_mem`：wOppSide_of_left_mem {s : AffineSub
space R P} {x : P} (y : P) (hx : x in s) : s.WOppSide x y
· 使用定理 `AffineSubspace.wSameSide_of_right_mem`：wSameSide_of_right_mem {s : Affin
eSubspace R P} (x : P) {y : P} (hy : y in s) : s.WSameSide x y
· 使用定理 `AffineSubspace.wOppSide_of_right_mem`：wOppSide_of_right_mem {s : AffineS
ubspace R P} (x : P) {y : P} (hy : y in s) : s.WOppSide x y
-/
theorem wSameSide_and_wOppSide_iff {s : AffineSubspace R P} {x y : P} :
    s.WSameSide x y ∧ s.WOppSide x y ↔ x ∈ s ∨ y ∈ s := by
  constructor
  · rintro ⟨hs, ho⟩
    rw [wOppSide_comm] at ho
    by_contra h
    rw [not_or] at h
    exact h.1 (wOppSide_self_iff.1 (hs.trans_wOppSide ho h.2))
  · rintro (h | h)
    · exact ⟨wSameSide_of_left_mem y h, wOppSide_of_left_mem y h⟩
    · exact ⟨wSameSide_of_right_mem x h, wOppSide_of_right_mem x h⟩
/-
**AffineSubspace.WSameSide.not_sOppSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e.WSameSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y : P}, s.WSameSide x y → ¬s.SOppSide x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.wSameSide_and_wOppSide_iff`：wSameSide_and_wOppSide_iff {s
 : AffineSubspace R P} {x y : P} : s.WSameSide x y ∧ s.WOppSide x y ↔ x in s ∨ y
 in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem WSameSide.not_sOppSide {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) :
    ¬s.SOppSide x y := by
  intro ho
  have hxy := wSameSide_and_wOppSide_iff.1 ⟨h, ho.1⟩
  rcases hxy with (hx | hy)
  · exact ho.2.1 hx
  · exact ho.2.2 hy
/-
**AffineSubspace.SSameSide.not_wOppSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e.SSameSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y : P}, s.SSameSide x y → ¬s.WOppSide x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.wSameSide_and_wOppSide_iff`：wSameSide_and_wOppSide_iff {s
 : AffineSubspace R P} {x y : P} : s.WSameSide x y ∧ s.WOppSide x y ↔ x in s ∨ y
 in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem SSameSide.not_wOppSide {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    ¬s.WOppSide x y := by
  intro ho
  have hxy := wSameSide_and_wOppSide_iff.1 ⟨h.1, ho⟩
  rcases hxy with (hx | hy)
  · exact h.2.1 hx
  · exact h.2.2 hy
/-
**AffineSubspace.SSameSide.not_sOppSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e.SSameSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y : P}, s.SSameSide x y → ¬s.SOppSide x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.SSameSide.not_wOppSide`：∀ {R : Type u_1} {V : Type u_2} {
P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrde
redRing R] [inst_3 : AddCom…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem SSameSide.not_sOppSide {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    ¬s.SOppSide x y :=
  fun ho => h.not_wOppSide ho.1
/-
**AffineSubspace.WOppSide.not_sSameSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e.WOppSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y : P}, s.WOppSide x y → ¬s.SSameSide x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.SSameSide.not_wOppSide`：∀ {R : Type u_1} {V : Type u_2} {
P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrde
redRing R] [inst_3 : AddCom…
-/
theorem WOppSide.not_sSameSide {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) :
    ¬s.SSameSide x y :=
  fun hs => hs.not_wOppSide h
/-
**AffineSubspace.SOppSide.not_wSameSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e.SOppSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y : P}, s.SOppSide x y → ¬s.WSameSide x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.WSameSide.not_sOppSide`：∀ {R : Type u_1} {V : Type u_2} {
P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrde
redRing R] [inst_3 : AddCom…
-/
theorem SOppSide.not_wSameSide {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    ¬s.WSameSide x y :=
  fun hs => hs.not_sOppSide h
/-
**AffineSubspace.SOppSide.not_sSameSide** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e.SOppSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y : P}, s.SOppSide x y → ¬s.SSameSide x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.SOppSide.not_wSameSide`：∀ {R : Type u_1} {V : Type u_2} {
P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrde
redRing R] [inst_3 : AddCom…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem SOppSide.not_sSameSide {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    ¬s.SSameSide x y :=
  fun hs => h.not_wSameSide hs.1

set_option backward.isDefEq.respectTransparency false in
/-
**AffineSubspace.wOppSide_iff_exists_wbtw** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：wOppSide_iff_exists_wbtw {s : AffineSubspace R P} {x y : P} : s.WOppSide x
 y ↔ exists p in s, Wbtw R x p y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `wbtw_self_left`：wbtw_self_left (x y : P) : Wbtw R x x y
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `wbtw_self_right`：wbtw_self_right (x y : P) : Wbtw R x y y
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.smul_const_eq`：smul_const_eq [SMul K α]
 (p : b = c) (s : K) : s • b = s • c
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.neg_eq_eval`：neg_eq_eval [AddCommGroup M] [Semi
ring S] [Module S M] [Ring R] [Module R M] {l : NF R M} {l₀ : NF S M} (hl : l.ev
al = l₀.eval) {x : M} (h :…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₁`：sub_eq_eval₁ [SMul R M] [AddGroup
 M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval - (a₂ ::ᵣ l₂).eval
 = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₂`：sub_eq_eval₂ [Ring R] [AddCommGro
up M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval - l₂.eval
 = l.eval) : ((r₁, x) ::ᵣ l…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_eq_eval`：zero_eq_eval [AddMonoid M] : (0:M
) = NF.eval (R
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_const`：eq_cons_const [AddCommMonoid M] 
[Semiring R] [Module R M] {r : R} (m : M) {n : M} {l : NF R M} (h1 : r = 0) (h2 
: l.eval = n) : ((r, m) ::ᵣ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 125 条，此处仅展示前 30 条）
-/
theorem wOppSide_iff_exists_wbtw {s : AffineSubspace R P} {x y : P} :
    s.WOppSide x y ↔ ∃ p ∈ s, Wbtw R x p y := by
  refine ⟨fun h => ?_, fun ⟨p, hp, h⟩ => h.wOppSide₁₃ hp⟩
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
  · rw [vsub_eq_zero_iff_eq] at h
    rw [h]
    exact ⟨p₁, hp₁, wbtw_self_left _ _ _⟩
  · rw [vsub_eq_zero_iff_eq] at h
    rw [← h]
    exact ⟨p₂, hp₂, wbtw_self_right _ _ _⟩
  · refine ⟨lineMap x y (r₂ / (r₁ + r₂)), ?_, ?_⟩
    · have : (r₂ / (r₁ + r₂)) • (y -ᵥ p₂ + (p₂ -ᵥ p₁) - (x -ᵥ p₁)) + (x -ᵥ p₁) =
          (r₂ / (r₁ + r₂)) • (p₂ -ᵥ p₁) := by
        rw [← neg_vsub_eq_vsub_rev p₂ y]
        linear_combination (norm := match_scalars <;> field) (r₁ + r₂)⁻¹ • h
      rw [lineMap_apply, ← vsub_vadd x p₁, ← vsub_vadd y p₂, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc,
        ← vadd_assoc, vadd_eq_add, this]
      exact s.smul_vsub_vadd_mem (r₂ / (r₁ + r₂)) hp₂ hp₁ hp₁
    · exact Set.mem_image_of_mem _
        ⟨by positivity,
          div_le_one_of_le₀ (le_add_of_nonneg_left hr₁.le) (Left.add_pos hr₁ hr₂).le⟩
/-
**AffineSubspace.SOppSide.exists_sbtw** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace.
SOppSide`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Field R] [inst_1 : 
LinearOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : AddCommGroup V] [ins
t_4 : _root_.Module R V] [inst_5 : AddTorsor V P]   {s : AffineSubspace R P} {x 
y : P}, s.SOppSide x y → ∃ p ∈ s, Sbtw R x p y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.wOppSide_iff_exists_wbtw`：wOppSide_iff_exists_wbtw {s : A
ffineSubspace R P} {x y : P} : s.WOppSide x y ↔ exists p in s, Wbtw R x p y
· 使用定理 `AffineSubspace.SOppSide.wOppSide`：∀ {R : Type u_1} {V : Type u_2} {P : T
ype u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrder
edRing R] [inst_3 : Ad…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem SOppSide.exists_sbtw {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    ∃ p ∈ s, Sbtw R x p y := by
  obtain ⟨p, hp, hw⟩ := wOppSide_iff_exists_wbtw.1 h.wOppSide
  refine ⟨p, hp, hw, ?_, ?_⟩
  · rintro rfl
    exact h.2.1 hp
  · rintro rfl
    exact h.2.2 hp
/-
**AffineSubspace._root_.Sbtw.sOppSide_of_notMem_of_mem** 是 Mathlib 中的一个定理，位于命名空间
 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Sbtw.sOppSide_of_notMem_of_mem {s : AffineSubspace R P} {x y z : P}
    (h : Sbtw R x y z) (hx : x ∉ s) (hy : y ∈ s) : s.SOppSide x z := by
  refine ⟨h.wbtw.wOppSide₁₃ hy, hx, fun hz => hx ?_⟩
  rcases h with ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hyx, hyz⟩
  rw [lineMap_apply] at hy
  have ht : t ≠ 1 := by
    rintro rfl
    simp [lineMap_apply] at hyz
  have hy' := vsub_mem_direction hy hz
  rw [vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev z, ← neg_one_smul R (z -ᵥ x), ← add_smul,
    ← sub_eq_add_neg, s.direction.smul_mem_iff (sub_ne_zero_of_ne ht)] at hy'
  rwa [vadd_mem_iff_mem_of_mem_direction (Submodule.smul_mem _ _ hy')] at hy
/-
**AffineSubspace.sSameSide_smul_vsub_vadd_left** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Subspace`。
形式化陈述：sSameSide_smul_vsub_vadd_left {s : AffineSubspace R P} {x p₁ p₂ : P} (hx :
 x ∉ s) (hp₁ : p₁ in s) (hp₂ : p₂ in s) {t : R} (ht : 0 < t) : s.SSameSide (t • 
(x -ᵥ p₁) +ᵥ p₂) x
参数：hx : x ∉ s；hp₁ : p₁ in s；hp₂ : p₂ in s；ht : 0 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.wSameSide_smul_vsub_vadd_left`：wSameSide_smul_vsub_vadd_l
eft {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s) (hp₂ : p₂ in s)
 {t : R} (ht : 0 <= t) : s.WSameSi…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.vsub_right_mem_direction_iff_mem`：vsub_right_mem_directio
n_iff_mem {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P) : p₂ -ᵥ p in s
.direction ↔ p₂ in s
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `AffineSubspace.vadd_mem_iff_mem_direction`：vadd_mem_iff_mem_direction {s
 : AffineSubspace k P} (v : V) {p : P} (hp : p in s) : v +ᵥ p in s ↔ v in s.dire
ction
-/
theorem sSameSide_smul_vsub_vadd_left {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : 0 < t) : s.SSameSide (t • (x -ᵥ p₁) +ᵥ p₂) x := by
  refine ⟨wSameSide_smul_vsub_vadd_left x hp₁ hp₂ ht.le, fun h => hx ?_, hx⟩
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne.symm,
    vsub_right_mem_direction_iff_mem hp₁] at h
/-
**AffineSubspace.sSameSide_smul_vsub_vadd_right** 是 Mathlib 中的一个定理，位于命名空间 `Affin
eSubspace`。
形式化陈述：sSameSide_smul_vsub_vadd_right {s : AffineSubspace R P} {x p₁ p₂ : P} (hx 
: x ∉ s) (hp₁ : p₁ in s) (hp₂ : p₂ in s) {t : R} (ht : 0 < t) : s.SSameSide x (t
 • (x -ᵥ p₁) +ᵥ p₂)
参数：hx : x ∉ s；hp₁ : p₁ in s；hp₂ : p₂ in s；ht : 0 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.SSameSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.sSameSide_smul_vsub_vadd_left`：sSameSide_smul_vsub_vadd_l
eft {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s) (hp₁ : p₁ in s) (hp₂ : p
₂ in s) {t : R} (ht : 0 < t) : s.S…
-/
theorem sSameSide_smul_vsub_vadd_right {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : 0 < t) : s.SSameSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (sSameSide_smul_vsub_vadd_left hx hp₁ hp₂ ht).symm

set_option backward.isDefEq.respectTransparency false in
/-
**AffineSubspace.sSameSide_lineMap_left** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e`。
形式化陈述：sSameSide_lineMap_left {s : AffineSubspace R P} {x y : P} (hx : x in s) (h
y : y ∉ s) {t : R} (ht : 0 < t) : s.SSameSide (lineMap x y t) y
参数：hx : x in s；hy : y ∉ s；ht : 0 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.sSameSide_smul_vsub_vadd_left`：sSameSide_smul_vsub_vadd_l
eft {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s) (hp₁ : p₁ in s) (hp₂ : p
₂ in s) {t : R} (ht : 0 < t) : s.S…
-/
theorem sSameSide_lineMap_left {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : 0 < t) : s.SSameSide (lineMap x y t) y :=
  sSameSide_smul_vsub_vadd_left hy hx hx ht

set_option backward.isDefEq.respectTransparency false in
/-
**AffineSubspace.sSameSide_lineMap_right** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspa
ce`。
形式化陈述：sSameSide_lineMap_right {s : AffineSubspace R P} {x y : P} (hx : x in s) (
hy : y ∉ s) {t : R} (ht : 0 < t) : s.SSameSide y (lineMap x y t)
参数：hx : x in s；hy : y ∉ s；ht : 0 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.SSameSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type
 u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedR
ing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.sSameSide_lineMap_left`：sSameSide_lineMap_left {s : Affin
eSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) {t : R} (ht : 0 < t) : s.SSa
meSide (lineMap x y t) y
-/
theorem sSameSide_lineMap_right {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : 0 < t) : s.SSameSide y (lineMap x y t) :=
  (sSameSide_lineMap_left hx hy ht).symm
/-
**AffineSubspace.sOppSide_smul_vsub_vadd_left** 是 Mathlib 中的一个定理，位于命名空间 `AffineS
ubspace`。
形式化陈述：sOppSide_smul_vsub_vadd_left {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : 
x ∉ s) (hp₁ : p₁ in s) (hp₂ : p₂ in s) {t : R} (ht : t < 0) : s.SOppSide (t • (x
 -ᵥ p₁) +ᵥ p₂) x
参数：hx : x ∉ s；hp₁ : p₁ in s；hp₂ : p₂ in s；ht : t < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.wOppSide_smul_vsub_vadd_left`：wOppSide_smul_vsub_vadd_lef
t {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s) (hp₂ : p₂ in s) {
t : R} (ht : t <= 0) : s.WOppSide…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.vsub_right_mem_direction_iff_mem`：vsub_right_mem_directio
n_iff_mem {s : AffineSubspace k P} {p : P} (hp : p in s) (p₂ : P) : p₂ -ᵥ p in s
.direction ↔ p₂ in s
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `AffineSubspace.vadd_mem_iff_mem_direction`：vadd_mem_iff_mem_direction {s
 : AffineSubspace k P} (v : V) {p : P} (hp : p in s) : v +ᵥ p in s ↔ v in s.dire
ction
-/
theorem sOppSide_smul_vsub_vadd_left {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : t < 0) : s.SOppSide (t • (x -ᵥ p₁) +ᵥ p₂) x := by
  refine ⟨wOppSide_smul_vsub_vadd_left x hp₁ hp₂ ht.le, fun h => hx ?_, hx⟩
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne,
    vsub_right_mem_direction_iff_mem hp₁] at h
/-
**AffineSubspace.sOppSide_smul_vsub_vadd_right** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Subspace`。
形式化陈述：sOppSide_smul_vsub_vadd_right {s : AffineSubspace R P} {x p₁ p₂ : P} (hx :
 x ∉ s) (hp₁ : p₁ in s) (hp₂ : p₂ in s) {t : R} (ht : t < 0) : s.SOppSide x (t •
 (x -ᵥ p₁) +ᵥ p₂)
参数：hx : x ∉ s；hp₁ : p₁ in s；hp₂ : p₂ in s；ht : t < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.SOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.sOppSide_smul_vsub_vadd_left`：sOppSide_smul_vsub_vadd_lef
t {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s) (hp₁ : p₁ in s) (hp₂ : p₂ 
in s) {t : R} (ht : t < 0) : s.SO…
-/
theorem sOppSide_smul_vsub_vadd_right {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : t < 0) : s.SOppSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (sOppSide_smul_vsub_vadd_left hx hp₁ hp₂ ht).symm

set_option backward.isDefEq.respectTransparency false in
/-
**AffineSubspace.sOppSide_lineMap_left** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
`。
形式化陈述：sOppSide_lineMap_left {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy
 : y ∉ s) {t : R} (ht : t < 0) : s.SOppSide (lineMap x y t) y
参数：hx : x in s；hy : y ∉ s；ht : t < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.sOppSide_smul_vsub_vadd_left`：sOppSide_smul_vsub_vadd_lef
t {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s) (hp₁ : p₁ in s) (hp₂ : p₂ 
in s) {t : R} (ht : t < 0) : s.SO…
-/
theorem sOppSide_lineMap_left {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : t < 0) : s.SOppSide (lineMap x y t) y :=
  sOppSide_smul_vsub_vadd_left hy hx hx ht

set_option backward.isDefEq.respectTransparency false in
/-
**AffineSubspace.sOppSide_lineMap_right** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e`。
形式化陈述：sOppSide_lineMap_right {s : AffineSubspace R P} {x y : P} (hx : x in s) (h
y : y ∉ s) {t : R} (ht : t < 0) : s.SOppSide y (lineMap x y t)
参数：hx : x in s；hy : y ∉ s；ht : t < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.SOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.sOppSide_lineMap_left`：sOppSide_lineMap_left {s : AffineS
ubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) {t : R} (ht : t < 0) : s.SOppS
ide (lineMap x y t) y
-/
theorem sOppSide_lineMap_right {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : t < 0) : s.SOppSide y (lineMap x y t) :=
  (sOppSide_lineMap_left hx hy ht).symm
/-
**AffineSubspace.setOfPred_wSameSide_eq_image2** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Subspace`。
形式化陈述：setOfPred_wSameSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉
 s) (hp : p in s) : { y | s.WSameSide x y } = Set.image2 (fun (t : R) q => t • (
x -ᵥ p) +ᵥ q) (Set.Ici 0) s
参数：hx : x ∉ s；hp : p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineSubspace.wSameSide_iff_exists_left`：wSameSide_iff_exists_left {s :
 AffineSubspace R P} {x y p₁ : P} (h : p₁ in s) : s.WSameSide x y ↔ x in s ∨ exi
sts p₂ in s, SameRay R (x -ᵥ p…
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `AffineSubspace.wSameSide_smul_vsub_vadd_right`：wSameSide_smul_vsub_vadd_
right {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s) (hp₂ : p₂ in 
s) {t : R} (ht : 0 <= t) : s.WSameS…
-/
theorem setOfPred_wSameSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.WSameSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Ici 0) s := by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Ici]
  constructor
  · rw [wSameSide_iff_exists_left hp, or_iff_right hx]
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      refine ⟨0, le_rfl, p₂, hp₂, ?_⟩
      simp [h]
    · refine ⟨r₁ / r₂, (div_pos hr₁ hr₂).le, p₂, hp₂, ?_⟩
      rw [div_eq_inv_mul, ← smul_smul, h, smul_smul, inv_mul_cancel₀ hr₂.ne.symm, one_smul,
        vsub_vadd]
  · rintro ⟨t, ht, p', hp', rfl⟩
    exact wSameSide_smul_vsub_vadd_right x hp hp' ht

@[deprecated (since := "2026-07-09")]
alias setOf_wSameSide_eq_image2 := setOfPred_wSameSide_eq_image2
/-
**AffineSubspace.setOfPred_sSameSide_eq_image2** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Subspace`。
形式化陈述：setOfPred_sSameSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉
 s) (hp : p in s) : { y | s.SSameSide x y } = Set.image2 (fun (t : R) q => t • (
x -ᵥ p) +ᵥ q) (Set.Ioi 0) s
参数：hx : x ∉ s；hp : p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineSubspace.sSameSide_iff_exists_left`：sSameSide_iff_exists_left {s :
 AffineSubspace R P} {x y p₁ : P} (h : p₁ in s) : s.SSameSide x y ↔ x ∉ s ∧ y ∉ 
s ∧ exists p₂ in s, SameRay R …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `AffineSubspace.sSameSide_smul_vsub_vadd_right`：sSameSide_smul_vsub_vadd_
right {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s) (hp₁ : p₁ in s) (hp₂ :
 p₂ in s) {t : R} (ht : 0 < t) : s.…
-/
theorem setOfPred_sSameSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.SSameSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Ioi 0) s := by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Ioi]
  constructor
  · rw [sSameSide_iff_exists_left hp]
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hy (h.symm ▸ hp₂))
    · refine ⟨r₁ / r₂, div_pos hr₁ hr₂, p₂, hp₂, ?_⟩
      rw [div_eq_inv_mul, ← smul_smul, h, smul_smul, inv_mul_cancel₀ hr₂.ne.symm, one_smul,
        vsub_vadd]
  · rintro ⟨t, ht, p', hp', rfl⟩
    exact sSameSide_smul_vsub_vadd_right hx hp hp' ht

@[deprecated (since := "2026-07-09")]
alias setOf_sSameSide_eq_image2 := setOfPred_sSameSide_eq_image2
/-
**AffineSubspace.setOfPred_wOppSide_eq_image2** 是 Mathlib 中的一个定理，位于命名空间 `AffineS
ubspace`。
形式化陈述：setOfPred_wOppSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ 
s) (hp : p in s) : { y | s.WOppSide x y } = Set.image2 (fun (t : R) q => t • (x 
-ᵥ p) +ᵥ q) (Set.Iic 0) s
参数：hx : x ∉ s；hp : p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineSubspace.wOppSide_iff_exists_left`：wOppSide_iff_exists_left {s : A
ffineSubspace R P} {x y p₁ : P} (h : p₁ in s) : s.WOppSide x y ↔ x in s ∨ exists
 p₂ in s, SameRay R (x -ᵥ p₁)…
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `div_neg_of_neg_of_pos`：div_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) :
 a / b < 0
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.neg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Ad
dLeftStrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
（共 39 条，此处仅展示前 30 条）
-/
theorem setOfPred_wOppSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.WOppSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Iic 0) s := by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Iic]
  constructor
  · rw [wOppSide_iff_exists_left hp, or_iff_right hx]
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      refine ⟨0, le_rfl, p₂, hp₂, ?_⟩
      simp [h]
    · refine ⟨-r₁ / r₂, (div_neg_of_neg_of_pos (Left.neg_neg_iff.2 hr₁) hr₂).le, p₂, hp₂, ?_⟩
      rw [div_eq_inv_mul, ← smul_smul, neg_smul, h, smul_neg, smul_smul,
        inv_mul_cancel₀ hr₂.ne.symm, one_smul, neg_vsub_eq_vsub_rev, vsub_vadd]
  · rintro ⟨t, ht, p', hp', rfl⟩
    exact wOppSide_smul_vsub_vadd_right x hp hp' ht

@[deprecated (since := "2026-07-09")]
alias setOf_wOppSide_eq_image2 := setOfPred_wOppSide_eq_image2
/-
**AffineSubspace.setOfPred_sOppSide_eq_image2** 是 Mathlib 中的一个定理，位于命名空间 `AffineS
ubspace`。
形式化陈述：setOfPred_sOppSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ 
s) (hp : p in s) : { y | s.SOppSide x y } = Set.image2 (fun (t : R) q => t • (x 
-ᵥ p) +ᵥ q) (Set.Iio 0) s
参数：hx : x ∉ s；hp : p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineSubspace.sOppSide_iff_exists_left`：sOppSide_iff_exists_left {s : A
ffineSubspace R P} {x y p₁ : P} (h : p₁ in s) : s.SOppSide x y ↔ x ∉ s ∧ y ∉ s ∧
 exists p₂ in s, SameRay R (x…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `div_neg_of_neg_of_pos`：div_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) :
 a / b < 0
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.neg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Ad
dLeftStrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `AffineSubspace.sOppSide_smul_vsub_vadd_right`：sOppSide_smul_vsub_vadd_ri
ght {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s) (hp₁ : p₁ in s) (hp₂ : p
₂ in s) {t : R} (ht : t < 0) : s.S…
-/
theorem setOfPred_sOppSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.SOppSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Iio 0) s := by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Iio]
  constructor
  · rw [sOppSide_iff_exists_left hp]
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hy (h ▸ hp₂))
    · refine ⟨-r₁ / r₂, div_neg_of_neg_of_pos (Left.neg_neg_iff.2 hr₁) hr₂, p₂, hp₂, ?_⟩
      rw [div_eq_inv_mul, ← smul_smul, neg_smul, h, smul_neg, smul_smul,
        inv_mul_cancel₀ hr₂.ne.symm, one_smul, neg_vsub_eq_vsub_rev, vsub_vadd]
  · rintro ⟨t, ht, p', hp', rfl⟩
    exact sOppSide_smul_vsub_vadd_right hx hp hp' ht

@[deprecated (since := "2026-07-09")]
alias setOf_sOppSide_eq_image2 := setOfPred_sOppSide_eq_image2
/-
**AffineSubspace.wOppSide_pointReflection** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：wOppSide_pointReflection {s : AffineSubspace R P} {x : P} (y : P) (hx : x 
in s) : s.WOppSide y (pointReflection R x y)
参数：y : P；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Wbtw.wOppSide₁₃`：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : 
CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3
 : Ad…
· 使用定理 `wbtw_pointReflection`：wbtw_pointReflection (x y : P) : Wbtw R y x (point
Reflection R x y)
-/
theorem wOppSide_pointReflection {s : AffineSubspace R P} {x : P} (y : P) (hx : x ∈ s) :
    s.WOppSide y (pointReflection R x y) :=
  (wbtw_pointReflection R _ _).wOppSide₁₃ hx
/-
**AffineSubspace.sOppSide_pointReflection** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：sOppSide_pointReflection {s : AffineSubspace R P} {x y : P} (hx : x in s) 
(hy : y ∉ s) : s.SOppSide y (pointReflection R x y)
参数：hx : x in s；hy : y ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sbtw.sOppSide_of_notMem_of_mem`：∀ {R : Type u_1} {V : Type u_2} {P : Typ
e u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrderedRing
 R] [inst_3 : AddCom…
· 使用定理 `sbtw_pointReflection_of_ne`：sbtw_pointReflection_of_ne {x y : P} (h : x 
!= y) : Sbtw R y x (pointReflection R x y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sOppSide_pointReflection {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) :
    s.SOppSide y (pointReflection R x y) := by
  refine (sbtw_pointReflection_of_ne R fun h => hy ?_).sOppSide_of_notMem_of_mem hy hx
  rwa [← h]

end LinearOrderedField

section Normed

variable [SeminormedAddCommGroup V] [NormedSpace ℝ V] [PseudoMetricSpace P]
variable [NormedAddTorsor V P]

/-
**AffineSubspace.isConnected_setOfPred_wSameSide** 是 Mathlib 中的一个定理，位于命名空间 `Affi
neSubspace`。
形式化陈述：isConnected_setOfPred_wSameSide {s : AffineSubspace Real P} (x : P) (h : (
s : Set P).Nonempty) : IsConnected { y | s.WSameSide x y }
参数：x : P；h : (s : Set P).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddTorsor.connectedSpace`：∀ (G : Type u_1) (P : Type u_2) [inst : AddGro
up G] [inst_1 : AddTorsor G P] [inst_2 : TopologicalSpace G]   [PreconnectedSpac
e G] [inst_4 :…
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `NormedSpace.instPathConnectedSpace`：∀ {E : Type u_1} [inst : SeminormedA
ddCommGroup E] [NormedSpace ℝ E], PathConnectedSpace E
· 使用定理 `IsTopologicalAddTorsor.toContinuousVAdd`：∀ {V : Type u_1} {inst : AddGro
up V} {inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : AddTorsor V P}   {i
nst_3 : TopologicalSpace P} […
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `isConnected_univ`：isConnected_univ [ConnectedSpace α] : IsConnected (uni
v : Set α)
· 使用定理 `AffineSubspace.setOfPred_wSameSide_eq_image2`：setOfPred_wSameSide_eq_ima
ge2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s) : { y | s.WSam
eSide x y } = Set.image2 (fun (t :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
· 使用定理 `IsConnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace 
α] [inst_1 : TopologicalSpace β] {s : Set α},   IsConnected s → ∀ (f : α → β), C
ontinuo…
· 使用定理 `IsConnected.prod`：IsConnected.prod [TopologicalSpace β] {s : Set α} {t :
 Set β} (hs : IsConnected s) (ht : IsConnected t) : IsConnected (s ×ˢ t)
· 使用定理 `isConnected_Ici`：isConnected_Ici : IsConnected (Ici a)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isConnected_iff_connectedSpace`：isConnected_iff_connectedSpace {s : Set 
α} : IsConnected s ↔ ConnectedSpace s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.vadd`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [inst : 
TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpace Y
] [in…
· 使用定理 `Continuous.smul`：Continuous.smul (hf : Continuous f) (hg : Continuous g)
 : Continuous (f • g)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
（共 31 条，此处仅展示前 30 条）
-/
theorem isConnected_setOfPred_wSameSide {s : AffineSubspace ℝ P} (x : P)
    (h : (s : Set P).Nonempty) :
    IsConnected { y | s.WSameSide x y } := by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  by_cases hx : x ∈ s
  · simp only [wSameSide_of_left_mem, hx]
    have := AddTorsor.connectedSpace V P
    exact isConnected_univ
  · rw [setOfPred_wSameSide_eq_image2 hx hp, ← Set.image_prod]
    refine (isConnected_Ici.prod (isConnected_iff_connectedSpace.2 ?_)).image _
      ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
    convert! AddTorsor.connectedSpace s.direction s

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_wSameSide := isConnected_setOfPred_wSameSide
/-
**AffineSubspace.isPreconnected_setOfPred_wSameSide** 是 Mathlib 中的一个定理，位于命名空间 `A
ffineSubspace`。
形式化陈述：isPreconnected_setOfPred_wSameSide (s : AffineSubspace Real P) (x : P) : I
sPreconnected { y | s.WSameSide x y }
参数：s : AffineSubspace Real P；x : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineSubspace.WSameSide.congr_simp`：∀ {R : Type u_1} {V : Type u_2} {P 
: Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOr
deredRing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.coe_eq_bot_iff`：coe_eq_bot_iff (Q : AffineSubspace k P) :
 (Q : Set P) = ∅ ↔ Q = ⊥
· 使用定理 `isPreconnected_empty`：isPreconnected_empty : IsPreconnected (∅ : Set α)
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `AffineSubspace.isConnected_setOfPred_wSameSide`：isConnected_setOfPred_wS
ameSide {s : AffineSubspace Real P} (x : P) (h : (s : Set P).Nonempty) : IsConne
cted { y | s.WSameSide x y }
-/
theorem isPreconnected_setOfPred_wSameSide (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.WSameSide x y } := by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_wSameSide_bot]
    exact isPreconnected_empty
  · exact (isConnected_setOfPred_wSameSide x h).isPreconnected

@[deprecated (since := "2026-07-09")]
alias isPreconnected_setOf_wSameSide := isPreconnected_setOfPred_wSameSide
/-
**AffineSubspace.isConnected_setOfPred_sSameSide** 是 Mathlib 中的一个定理，位于命名空间 `Affi
neSubspace`。
形式化陈述：isConnected_setOfPred_sSameSide {s : AffineSubspace Real P} {x : P} (hx : 
x ∉ s) (h : (s : Set P).Nonempty) : IsConnected { y | s.SSameSide x y }
参数：hx : x ∉ s；h : (s : Set P).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.setOfPred_sSameSide_eq_image2`：setOfPred_sSameSide_eq_ima
ge2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s) : { y | s.SSam
eSide x y } = Set.image2 (fun (t :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
· 使用定理 `IsConnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace 
α] [inst_1 : TopologicalSpace β] {s : Set α},   IsConnected s → ∀ (f : α → β), C
ontinuo…
· 使用定理 `IsConnected.prod`：IsConnected.prod [TopologicalSpace β] {s : Set α} {t :
 Set β} (hs : IsConnected s) (ht : IsConnected t) : IsConnected (s ×ˢ t)
· 使用定理 `isConnected_Ioi`：isConnected_Ioi [NoMaxOrder α] : IsConnected (Ioi a)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isConnected_iff_connectedSpace`：isConnected_iff_connectedSpace {s : Set 
α} : IsConnected s ↔ ConnectedSpace s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `AddTorsor.connectedSpace`：∀ (G : Type u_1) (P : Type u_2) [inst : AddGro
up G] [inst_1 : AddTorsor G P] [inst_2 : TopologicalSpace G]   [PreconnectedSpac
e G] [inst_4 :…
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `NormedSpace.instPathConnectedSpace`：∀ {E : Type u_1} [inst : SeminormedA
ddCommGroup E] [NormedSpace ℝ E], PathConnectedSpace E
· 使用定理 `IsTopologicalAddTorsor.toContinuousVAdd`：∀ {V : Type u_1} {inst : AddGro
up V} {inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : AddTorsor V P}   {i
nst_3 : TopologicalSpace P} […
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.vadd`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [inst : 
TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpace Y
] [in…
· 使用定理 `Continuous.smul`：Continuous.smul (hf : Continuous f) (hg : Continuous g)
 : Continuous (f • g)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
（共 31 条，此处仅展示前 30 条）
-/
theorem isConnected_setOfPred_sSameSide {s : AffineSubspace ℝ P} {x : P} (hx : x ∉ s)
    (h : (s : Set P).Nonempty) : IsConnected { y | s.SSameSide x y } := by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  rw [setOfPred_sSameSide_eq_image2 hx hp, ← Set.image_prod]
  refine (isConnected_Ioi.prod (isConnected_iff_connectedSpace.2 ?_)).image _
    ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
  convert! AddTorsor.connectedSpace s.direction s

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_sSameSide := isConnected_setOfPred_sSameSide
/-
**AffineSubspace.isPreconnected_setOfPred_sSameSide** 是 Mathlib 中的一个定理，位于命名空间 `A
ffineSubspace`。
形式化陈述：isPreconnected_setOfPred_sSameSide (s : AffineSubspace Real P) (x : P) : I
sPreconnected { y | s.SSameSide x y }
参数：s : AffineSubspace Real P；x : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineSubspace.SSameSide.congr_simp`：∀ {R : Type u_1} {V : Type u_2} {P 
: Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOr
deredRing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.coe_eq_bot_iff`：coe_eq_bot_iff (Q : AffineSubspace k P) :
 (Q : Set P) = ∅ ↔ Q = ⊥
· 使用定理 `isPreconnected_empty`：isPreconnected_empty : IsPreconnected (∅ : Set α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `AffineSubspace.isConnected_setOfPred_sSameSide`：isConnected_setOfPred_sS
ameSide {s : AffineSubspace Real P} {x : P} (hx : x ∉ s) (h : (s : Set P).Nonemp
ty) : IsConnected { y | s.SSameSide …
-/
theorem isPreconnected_setOfPred_sSameSide (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.SSameSide x y } := by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_sSameSide_bot]
    exact isPreconnected_empty
  · by_cases hx : x ∈ s
    · simp only [hx, SSameSide, not_true, false_and, and_false]
      exact isPreconnected_empty
    · exact (isConnected_setOfPred_sSameSide hx h).isPreconnected

@[deprecated (since := "2026-07-09")]
alias isPreconnected_setOf_sSameSide := isPreconnected_setOfPred_sSameSide
/-
**AffineSubspace.isConnected_setOfPred_wOppSide** 是 Mathlib 中的一个定理，位于命名空间 `Affin
eSubspace`。
形式化陈述：isConnected_setOfPred_wOppSide {s : AffineSubspace Real P} (x : P) (h : (s
 : Set P).Nonempty) : IsConnected { y | s.WOppSide x y }
参数：x : P；h : (s : Set P).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddTorsor.connectedSpace`：∀ (G : Type u_1) (P : Type u_2) [inst : AddGro
up G] [inst_1 : AddTorsor G P] [inst_2 : TopologicalSpace G]   [PreconnectedSpac
e G] [inst_4 :…
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `NormedSpace.instPathConnectedSpace`：∀ {E : Type u_1} [inst : SeminormedA
ddCommGroup E] [NormedSpace ℝ E], PathConnectedSpace E
· 使用定理 `IsTopologicalAddTorsor.toContinuousVAdd`：∀ {V : Type u_1} {inst : AddGro
up V} {inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : AddTorsor V P}   {i
nst_3 : TopologicalSpace P} […
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `isConnected_univ`：isConnected_univ [ConnectedSpace α] : IsConnected (uni
v : Set α)
· 使用定理 `AffineSubspace.setOfPred_wOppSide_eq_image2`：setOfPred_wOppSide_eq_image
2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s) : { y | s.WOppSi
de x y } = Set.image2 (fun (t : R…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
· 使用定理 `IsConnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace 
α] [inst_1 : TopologicalSpace β] {s : Set α},   IsConnected s → ∀ (f : α → β), C
ontinuo…
· 使用定理 `IsConnected.prod`：IsConnected.prod [TopologicalSpace β] {s : Set α} {t :
 Set β} (hs : IsConnected s) (ht : IsConnected t) : IsConnected (s ×ˢ t)
· 使用定理 `isConnected_Iic`：isConnected_Iic : IsConnected (Iic a)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isConnected_iff_connectedSpace`：isConnected_iff_connectedSpace {s : Set 
α} : IsConnected s ↔ ConnectedSpace s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.vadd`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [inst : 
TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpace Y
] [in…
· 使用定理 `Continuous.smul`：Continuous.smul (hf : Continuous f) (hg : Continuous g)
 : Continuous (f • g)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
（共 31 条，此处仅展示前 30 条）
-/
theorem isConnected_setOfPred_wOppSide {s : AffineSubspace ℝ P} (x : P) (h : (s : Set P).Nonempty) :
    IsConnected { y | s.WOppSide x y } := by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  by_cases hx : x ∈ s
  · simp only [wOppSide_of_left_mem, hx]
    have := AddTorsor.connectedSpace V P
    exact isConnected_univ
  · rw [setOfPred_wOppSide_eq_image2 hx hp, ← Set.image_prod]
    refine (isConnected_Iic.prod (isConnected_iff_connectedSpace.2 ?_)).image _
      ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
    convert! AddTorsor.connectedSpace s.direction s

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_wOppSide := isConnected_setOfPred_wOppSide
/-
**AffineSubspace.isPreconnected_setOfPred_wOppSide** 是 Mathlib 中的一个定理，位于命名空间 `Af
fineSubspace`。
形式化陈述：isPreconnected_setOfPred_wOppSide (s : AffineSubspace Real P) (x : P) : Is
Preconnected { y | s.WOppSide x y }
参数：s : AffineSubspace Real P；x : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineSubspace.WOppSide.congr_simp`：∀ {R : Type u_1} {V : Type u_2} {P :
 Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrd
eredRing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.coe_eq_bot_iff`：coe_eq_bot_iff (Q : AffineSubspace k P) :
 (Q : Set P) = ∅ ↔ Q = ⊥
· 使用定理 `isPreconnected_empty`：isPreconnected_empty : IsPreconnected (∅ : Set α)
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `AffineSubspace.isConnected_setOfPred_wOppSide`：isConnected_setOfPred_wOp
pSide {s : AffineSubspace Real P} (x : P) (h : (s : Set P).Nonempty) : IsConnect
ed { y | s.WOppSide x y }
-/
theorem isPreconnected_setOfPred_wOppSide (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.WOppSide x y } := by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_wOppSide_bot]
    exact isPreconnected_empty
  · exact (isConnected_setOfPred_wOppSide x h).isPreconnected

@[deprecated (since := "2026-07-09")]
alias isPreconnected_setOf_wOppSide := isPreconnected_setOfPred_wOppSide
/-
**AffineSubspace.isConnected_setOfPred_sOppSide** 是 Mathlib 中的一个定理，位于命名空间 `Affin
eSubspace`。
形式化陈述：isConnected_setOfPred_sOppSide {s : AffineSubspace Real P} {x : P} (hx : x
 ∉ s) (h : (s : Set P).Nonempty) : IsConnected { y | s.SOppSide x y }
参数：hx : x ∉ s；h : (s : Set P).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.setOfPred_sOppSide_eq_image2`：setOfPred_sOppSide_eq_image
2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s) : { y | s.SOppSi
de x y } = Set.image2 (fun (t : R…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
· 使用定理 `IsConnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace 
α] [inst_1 : TopologicalSpace β] {s : Set α},   IsConnected s → ∀ (f : α → β), C
ontinuo…
· 使用定理 `IsConnected.prod`：IsConnected.prod [TopologicalSpace β] {s : Set α} {t :
 Set β} (hs : IsConnected s) (ht : IsConnected t) : IsConnected (s ×ˢ t)
· 使用定理 `isConnected_Iio`：isConnected_Iio [NoMinOrder α] : IsConnected (Iio a)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isConnected_iff_connectedSpace`：isConnected_iff_connectedSpace {s : Set 
α} : IsConnected s ↔ ConnectedSpace s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `AddTorsor.connectedSpace`：∀ (G : Type u_1) (P : Type u_2) [inst : AddGro
up G] [inst_1 : AddTorsor G P] [inst_2 : TopologicalSpace G]   [PreconnectedSpac
e G] [inst_4 :…
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `NormedSpace.instPathConnectedSpace`：∀ {E : Type u_1} [inst : SeminormedA
ddCommGroup E] [NormedSpace ℝ E], PathConnectedSpace E
· 使用定理 `IsTopologicalAddTorsor.toContinuousVAdd`：∀ {V : Type u_1} {inst : AddGro
up V} {inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : AddTorsor V P}   {i
nst_3 : TopologicalSpace P} […
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.vadd`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [inst : 
TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpace Y
] [in…
· 使用定理 `Continuous.smul`：Continuous.smul (hf : Continuous f) (hg : Continuous g)
 : Continuous (f • g)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
（共 31 条，此处仅展示前 30 条）
-/
theorem isConnected_setOfPred_sOppSide {s : AffineSubspace ℝ P} {x : P} (hx : x ∉ s)
    (h : (s : Set P).Nonempty) : IsConnected { y | s.SOppSide x y } := by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  rw [setOfPred_sOppSide_eq_image2 hx hp, ← Set.image_prod]
  refine (isConnected_Iio.prod (isConnected_iff_connectedSpace.2 ?_)).image _
    ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
  convert! AddTorsor.connectedSpace s.direction s

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_sOppSide := isConnected_setOfPred_sOppSide
/-
**AffineSubspace.isPreconnected_setOfPred_sOppSide** 是 Mathlib 中的一个定理，位于命名空间 `Af
fineSubspace`。
形式化陈述：isPreconnected_setOfPred_sOppSide (s : AffineSubspace Real P) (x : P) : Is
Preconnected { y | s.SOppSide x y }
参数：s : AffineSubspace Real P；x : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineSubspace.SOppSide.congr_simp`：∀ {R : Type u_1} {V : Type u_2} {P :
 Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrd
eredRing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.coe_eq_bot_iff`：coe_eq_bot_iff (Q : AffineSubspace k P) :
 (Q : Set P) = ∅ ↔ Q = ⊥
· 使用定理 `isPreconnected_empty`：isPreconnected_empty : IsPreconnected (∅ : Set α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `AffineSubspace.isConnected_setOfPred_sOppSide`：isConnected_setOfPred_sOp
pSide {s : AffineSubspace Real P} {x : P} (hx : x ∉ s) (h : (s : Set P).Nonempty
) : IsConnected { y | s.SOppSide x …
-/
theorem isPreconnected_setOfPred_sOppSide (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.SOppSide x y } := by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_sOppSide_bot]
    exact isPreconnected_empty
  · by_cases hx : x ∈ s
    · simp only [hx, SOppSide, not_true, false_and, and_false]
      exact isPreconnected_empty
    · exact (isConnected_setOfPred_sOppSide hx h).isPreconnected

@[deprecated (since := "2026-07-09")]
alias isPreconnected_setOf_sOppSide := isPreconnected_setOfPred_sOppSide

end Normed

end AffineSubspace

namespace Affine.Simplex

open AffineSubspace

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]
variable [AddTorsor V P] {n : ℕ} [NeZero n] (s : Simplex R P n)

set_option backward.isDefEq.respectTransparency false in
/-
**Affine.Simplex.sSameSide_affineSpan_faceOpposite_of_sign_eq** 是 Mathlib 中的一个引理
，位于命名空间 `Affine.Simplex`。
形式化陈述：sSameSide_affineSpan_faceOpposite_of_sign_eq {w₁ w₂ : Fin (n + 1) -> R} (h
w₁ : ∑ j, w₁ j = 1) (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} (hs : SignType.sign 
(w₁ i) = SignType.sign (w₂ i)) (h0 : w₁ i != 0) : (affineSpan R (Set.range (s.fa
ceOpposite i).points)).SSameSide (Finset.univ.affineCombination R s.points w₁) (
Finset.univ.affineCombination R s.points w₂)
参数：n + 1；hw₁ : ∑ j, w₁ j = 1；hw₂ : ∑ j, w₂ j = 1；n + 1；hs : SignType.sign (w₁ i)
 = SignType.sign (w₂ i)；h0 : w₁ i != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AffineSubspace.wSameSide_iff_exists_left`：wSameSide_iff_exists_left {s :
 AffineSubspace R P} {x y p₁ : P} (h : p₁ in s) : s.WSameSide x y ↔ x in s ∨ exi
sts p₂ in s, SameRay R (x -ᵥ p…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.affineCombination_vsub`：affineCombination_vsub (w₁ w₂ : ι -> k) (
p : ι -> P) : s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weigh
tedVSub p (w₁ - w₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] [inst_1 : DecidableEq ι] (a : ι) (x : M) (s : Finset ι),   ∑ a' ∈ s, Pi.
single a x …
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 68 条，此处仅展示前 30 条）
-/
lemma sSameSide_affineSpan_faceOpposite_of_sign_eq {w₁ w₂ : Fin (n + 1) → R} (hw₁ : ∑ j, w₁ j = 1)
    (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} (hs : SignType.sign (w₁ i) = SignType.sign (w₂ i))
    (h0 : w₁ i ≠ 0) :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SSameSide
      (Finset.univ.affineCombination R s.points w₁)
      (Finset.univ.affineCombination R s.points w₂) := by
  have h0' : w₂ i ≠ 0 := by intro h; simp_all
  refine ⟨?_, (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.2 h0,
    (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).not.2 h0'⟩
  obtain ⟨j, hj⟩ : ∃ j, j ≠ i := exists_ne _
  have hj' : s.points j ∈ affineSpan R (Set.range (s.faceOpposite i).points) := by
    simpa using hj
  refine (wSameSide_iff_exists_left hj').2 (.inr ?_)
  rw [← Finset.univ.affineCombination_piSingle R s.points
    (Finset.mem_univ j), Finset.affineCombination_vsub]
  let w₃ : Fin (n + 1) → R :=
    w₂ - w₂ i • (w₁ i)⁻¹ • (w₁ - Pi.single j 1)
  have hw₃1 : ∑ k, w₃ k = 1 := by simp [w₃, hw₂, ← Finset.mul_sum, hw₁]
  have hw₃i : w₃ i = 0 := by simp [w₃, hj.symm, h0]
  refine ⟨Finset.univ.affineCombination R s.points w₃,
    (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₃1).2 hw₃i, ?_⟩
  simp only [w₃, Finset.affineCombination_vsub, sub_sub_cancel, smul_smul, map_smul,
    sameRay_smul_right_iff]
  left
  rcases h0.lt_or_gt with h | h
  · rw [sign_neg h, eq_comm, sign_eq_neg_one_iff] at hs
    exact (mul_pos_of_neg_of_neg hs (inv_neg''.2 h)).le
  · rw [sign_pos h, eq_comm, sign_eq_one_iff] at hs
    positivity

set_option backward.isDefEq.respectTransparency false in
/-
**Affine.Simplex.sOppSide_affineSpan_faceOpposite_of_pos_of_neg** 是 Mathlib 中的一个
引理，位于命名空间 `Affine.Simplex`。
形式化陈述：sOppSide_affineSpan_faceOpposite_of_pos_of_neg {w₁ w₂ : Fin (n + 1) -> R} 
(hw₁ : ∑ j, w₁ j = 1) (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} (hs₁ : 0 < w₁ i) (
hs₂ : w₂ i < 0) : (affineSpan R (Set.range (s.faceOpposite i).points)).SOppSide 
(Finset.univ.affineCombination R s.points w₁) (Finset.univ.affineCombination R s
.points w₂)
参数：n + 1；hw₁ : ∑ j, w₁ j = 1；hw₂ : ∑ j, w₂ j = 1；n + 1；hs₁ : 0 < w₁ i；hs₂ : w₂ i
 < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sbtw_lineMap_iff`：sbtw_lineMap_iff : Sbtw R x (lineMap x y r) y ↔ x != y
 ∧ r in Set.Ioo (0 : R) 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用引理 `Set.InjOn.sbtw_map_iff`：Set.InjOn.sbtw_map_iff {x y z : P} {f : P ->ᵃ[R]
 P'} {s : AffineSubspace R P} (hf : Set.InjOn f s) (hx : x in s) (hy : y in s) (
hz : z in s)…
· 使用引理 `AffineIndependent.injOn_affineCombination_fintypeAffineCoords`：AffineInd
ependent.injOn_affineCombination_fintypeAffineCoords [Fintype ι] {p : ι -> P} (h
 : AffineIndependent k p) : InjOn (Finset.univ.affi…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用引理 `mem_fintypeAffineCoords_iff_sum`：mem_fintypeAffineCoords_iff_sum [Fintyp
e ι] {w : ι -> k} : w in fintypeAffineCoords ι k ↔ ∑ i, w i = 1
· 使用定理 `Sbtw.sOppSide_of_notMem_of_mem`：∀ {R : Type u_1} {V : Type u_2} {P : Typ
e u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrderedRing
 R] [inst_3 : AddCom…
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Affine.Simplex.affineCombination_mem_affineSpan_faceOpposite_iff`：affine
Combination_mem_affineSpan_faceOpposite_iff {n : Nat} [NeZero n] {s : Simplex k 
P n} {w : Fin (n + 1) -> k} (hw : ∑ i, w i = 1) {i : F…
（共 36 条，此处仅展示前 30 条）
-/
lemma sOppSide_affineSpan_faceOpposite_of_pos_of_neg {w₁ w₂ : Fin (n + 1) → R}
    (hw₁ : ∑ j, w₁ j = 1) (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} (hs₁ : 0 < w₁ i)
    (hs₂ : w₂ i < 0) :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SOppSide
      (Finset.univ.affineCombination R s.points w₁)
      (Finset.univ.affineCombination R s.points w₂) := by
  let w₃ : Fin (n + 1) → R := lineMap w₁ w₂ (w₁ i / (w₁ i - w₂ i))
  have hp : 0 < w₁ i - w₂ i := by grind
  have hw₃ : ∑ j, w₃ j = 1 := by
    simp [w₃, lineMap_apply, Finset.sum_add_distrib, ← Finset.mul_sum, hw₁, hw₂]
  have h : Sbtw R w₁ w₃ w₂ := sbtw_lineMap_iff.2
    ⟨(by grind), div_pos hs₁ hp, (div_lt_one hp).2 (by grind)⟩
  have h' : Sbtw R (Finset.univ.affineCombination R s.points w₁)
      (Finset.univ.affineCombination R s.points w₃)
      (Finset.univ.affineCombination R s.points w₂) := by
    rwa [s.independent.injOn_affineCombination_fintypeAffineCoords.sbtw_map_iff
     (mem_fintypeAffineCoords_iff_sum.2 hw₁) (mem_fintypeAffineCoords_iff_sum.2 hw₃)
     (mem_fintypeAffineCoords_iff_sum.2 hw₂)]
  refine h'.sOppSide_of_notMem_of_mem
    ((s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.2 hs₁.ne')
    ((s.affineCombination_mem_affineSpan_faceOpposite_iff hw₃).2 ?_)
  simp only [lineMap_apply, vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, w₃]
  rw [← neg_sub (w₁ i) (w₂ i), mul_neg, div_mul_cancel₀ _ hp.ne']
  simp
/-
**Affine.Simplex.sSameSide_affineSpan_faceOpposite_iff** 是 Mathlib 中的一个引理，位于命名空间
 `Affine.Simplex`。
形式化陈述：sSameSide_affineSpan_faceOpposite_iff {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ 
j, w₁ j = 1) (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} : (affineSpan R (Set.range 
(s.faceOpposite i).points)).SSameSide (Finset.univ.affineCombination R s.points 
w₁) (Finset.univ.affineCombination R s.points w₂) ↔ SignType.sign (w₁ i) = SignT
ype.sign (w₂ i) ∧ w₁ i != 0
参数：n + 1；hw₁ : ∑ j, w₁ j = 1；hw₂ : ∑ j, w₂ j = 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Affine.Simplex.affineCombination_mem_affineSpan_faceOpposite_iff`：affine
Combination_mem_affineSpan_faceOpposite_iff {n : Nat} [NeZero n] {s : Simplex k 
P n} {w : Fin (n + 1) -> k} (hw : ∑ i, w i = 1) {i : F…
· 使用定理 `AffineSubspace.SSameSide.left_notMem`：∀ {R : Type u_1} {V : Type u_2} {P
 : Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictO
rderedRing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.SSameSide.right_notMem`：∀ {R : Type u_1} {V : Type u_2} {
P : Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrict
OrderedRing R] [inst_3 : Ad…
· 使用引理 `sign_eq_sign_or_eq_neg`：sign_eq_sign_or_eq_neg {b : α} (ha : a != 0) (hb
 : b != 0) : sign a = sign b ∨ sign a = -sign b
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `AffineSubspace.WOppSide.not_sSameSide`：∀ {R : Type u_1} {V : Type u_2} {
P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrde
redRing R] [inst_3 : AddCom…
· 使用定理 `AffineSubspace.SOppSide.wOppSide`：∀ {R : Type u_1} {V : Type u_2} {P : T
ype u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrder
edRing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.SOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用引理 `Affine.Simplex.sOppSide_affineSpan_faceOpposite_of_pos_of_neg`：sOppSide_
affineSpan_faceOpposite_of_pos_of_neg {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ 
j = 1) (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} (hs₁…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_eq_one_iff`：sign_eq_one_iff : sign a = 1 ↔ 0 < a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用定理 `sign_eq_neg_one_iff`：sign_eq_neg_one_iff : sign a = -1 ↔ a < 0
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用引理 `Affine.Simplex.sSameSide_affineSpan_faceOpposite_of_sign_eq`：sSameSide_a
ffineSpan_faceOpposite_of_sign_eq {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 
1) (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} (hs : …
-/
lemma sSameSide_affineSpan_faceOpposite_iff {w₁ w₂ : Fin (n + 1) → R} (hw₁ : ∑ j, w₁ j = 1)
    (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SSameSide
      (Finset.univ.affineCombination R s.points w₁)
      (Finset.univ.affineCombination R s.points w₂) ↔
        SignType.sign (w₁ i) = SignType.sign (w₂ i) ∧ w₁ i ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨hs, h0⟩ ↦ s.sSameSide_affineSpan_faceOpposite_of_sign_eq hw₁ hw₂ hs h0⟩
  have h0 : w₁ i ≠ 0 :=
    (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.1 h.left_notMem
  refine ⟨?_, h0⟩
  have h0' : w₂ i ≠ 0 :=
    (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).not.1 h.right_notMem
  rcases sign_eq_sign_or_eq_neg h0 h0' with hs | hs
  · exact hs
  · exfalso
    rcases Ne.lt_or_gt h0 with h' | h'
    · rw [sign_neg h', neg_inj, eq_comm, sign_eq_one_iff] at hs
      exact (s.sOppSide_affineSpan_faceOpposite_of_pos_of_neg
        hw₂ hw₁ hs h').symm.wOppSide.not_sSameSide h
    · rw [sign_pos h', eq_comm, neg_eq_iff_eq_neg, sign_eq_neg_one_iff] at hs
      exact (s.sOppSide_affineSpan_faceOpposite_of_pos_of_neg
        hw₁ hw₂ h' hs).wOppSide.not_sSameSide h
/-
**Affine.Simplex.sOppSide_affineSpan_faceOpposite_iff** 是 Mathlib 中的一个引理，位于命名空间 
`Affine.Simplex`。
形式化陈述：sOppSide_affineSpan_faceOpposite_iff {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j
, w₁ j = 1) (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (
s.faceOpposite i).points)).SOppSide (Finset.univ.affineCombination R s.points w₁
) (Finset.univ.affineCombination R s.points w₂) ↔ SignType.sign (w₁ i) = -SignTy
pe.sign (w₂ i) ∧ w₁ i != 0
参数：n + 1；hw₁ : ∑ j, w₁ j = 1；hw₂ : ∑ j, w₂ j = 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Affine.Simplex.affineCombination_mem_affineSpan_faceOpposite_iff`：affine
Combination_mem_affineSpan_faceOpposite_iff {n : Nat} [NeZero n] {s : Simplex k 
P n} {w : Fin (n + 1) -> k} (hw : ∑ i, w i = 1) {i : F…
· 使用定理 `AffineSubspace.SOppSide.left_notMem`：∀ {R : Type u_1} {V : Type u_2} {P 
: Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOr
deredRing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.SOppSide.right_notMem`：∀ {R : Type u_1} {V : Type u_2} {P
 : Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictO
rderedRing R] [inst_3 : Ad…
· 使用引理 `sign_eq_sign_or_eq_neg`：sign_eq_sign_or_eq_neg {b : α} (ha : a != 0) (hb
 : b != 0) : sign a = sign b ∨ sign a = -sign b
· 使用定理 `AffineSubspace.WSameSide.not_sOppSide`：∀ {R : Type u_1} {V : Type u_2} {
P : Type u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrde
redRing R] [inst_3 : AddCom…
· 使用定理 `AffineSubspace.SSameSide.wSameSide`：∀ {R : Type u_1} {V : Type u_2} {P :
 Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrd
eredRing R] [inst_3 : Ad…
· 使用引理 `Affine.Simplex.sSameSide_affineSpan_faceOpposite_of_sign_eq`：sSameSide_a
ffineSpan_faceOpposite_of_sign_eq {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 
1) (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} (hs : …
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `AffineSubspace.SOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用引理 `Affine.Simplex.sOppSide_affineSpan_faceOpposite_of_pos_of_neg`：sOppSide_
affineSpan_faceOpposite_of_pos_of_neg {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ 
j = 1) (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} (hs₁…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_eq_one_iff`：sign_eq_one_iff : sign a = 1 ↔ 0 < a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用定理 `sign_eq_neg_one_iff`：sign_eq_neg_one_iff : sign a = -1 ↔ a < 0
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
-/
lemma sOppSide_affineSpan_faceOpposite_iff {w₁ w₂ : Fin (n + 1) → R} (hw₁ : ∑ j, w₁ j = 1)
    (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SOppSide
      (Finset.univ.affineCombination R s.points w₁)
      (Finset.univ.affineCombination R s.points w₂) ↔
        SignType.sign (w₁ i) = -SignType.sign (w₂ i) ∧ w₁ i ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨hs, h0⟩ ↦ ?_⟩
  · have h0 : w₁ i ≠ 0 :=
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.1 h.left_notMem
    refine ⟨?_, h0⟩
    have h0' : w₂ i ≠ 0 :=
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).not.1 h.right_notMem
    rcases sign_eq_sign_or_eq_neg h0 h0' with hs | hs
    · exfalso
      exact (s.sSameSide_affineSpan_faceOpposite_of_sign_eq hw₁ hw₂ hs h0).wSameSide.not_sOppSide h
    · exact hs
  · rcases h0.lt_or_gt with h' | h'
    · rw [sign_neg h', neg_inj, eq_comm, sign_eq_one_iff] at hs
      exact (s.sOppSide_affineSpan_faceOpposite_of_pos_of_neg hw₂ hw₁ hs h').symm
    · rw [sign_pos h', eq_comm, neg_eq_iff_eq_neg, sign_eq_neg_one_iff] at hs
      exact s.sOppSide_affineSpan_faceOpposite_of_pos_of_neg hw₁ hw₂ h' hs
/-
**Affine.Simplex.wSameSide_affineSpan_faceOpposite_iff** 是 Mathlib 中的一个引理，位于命名空间
 `Affine.Simplex`。
形式化陈述：wSameSide_affineSpan_faceOpposite_iff {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ 
j, w₁ j = 1) (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} : (affineSpan R (Set.range 
(s.faceOpposite i).points)).WSameSide (Finset.univ.affineCombination R s.points 
w₁) (Finset.univ.affineCombination R s.points w₂) ↔ SignType.sign (w₁ i) = SignT
ype.sign (w₂ i) ∨ w₁ i = 0 ∨ w₂ i = 0
参数：n + 1；hw₁ : ∑ j, w₁ j = 1；hw₂ : ∑ j, w₂ j = 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Affine.Simplex.sSameSide_affineSpan_faceOpposite_iff`：sSameSide_affineSp
an_faceOpposite_iff {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1) (hw₂ : ∑ j,
 w₂ j = 1) {i : Fin (n + 1)} : (affineSpan…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Affine.Simplex.affineCombination_mem_affineSpan_faceOpposite_iff`：affine
Combination_mem_affineSpan_faceOpposite_iff {n : Nat} [NeZero n] {s : Simplex k 
P n} {w : Fin (n + 1) -> k} (hw : ∑ i, w i = 1) {i : F…
· 使用定理 `AffineSubspace.wSameSide_of_left_mem`：wSameSide_of_left_mem {s : AffineS
ubspace R P} {x : P} (y : P) (hx : x in s) : s.WSameSide x y
· 使用定理 `AffineSubspace.wSameSide_of_right_mem`：wSameSide_of_right_mem {s : Affin
eSubspace R P} (x : P) {y : P} (hy : y in s) : s.WSameSide x y
· 使用定理 `AffineSubspace.SSameSide.wSameSide`：∀ {R : Type u_1} {V : Type u_2} {P :
 Type u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrd
eredRing R] [inst_3 : Ad…
· 使用引理 `Affine.Simplex.sSameSide_affineSpan_faceOpposite_of_sign_eq`：sSameSide_a
ffineSpan_faceOpposite_of_sign_eq {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 
1) (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} (hs : …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma wSameSide_affineSpan_faceOpposite_iff {w₁ w₂ : Fin (n + 1) → R} (hw₁ : ∑ j, w₁ j = 1)
    (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).WSameSide
      (Finset.univ.affineCombination R s.points w₁)
      (Finset.univ.affineCombination R s.points w₂) ↔
        SignType.sign (w₁ i) = SignType.sign (w₂ i) ∨ w₁ i = 0 ∨ w₂ i = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_cases h0 : w₁ i = 0
    · simp [h0]
    by_cases h0' : w₂ i = 0
    · simp [h0']
    exact .inl ((s.sSameSide_affineSpan_faceOpposite_iff hw₁ hw₂).1 ⟨h,
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.2 h0,
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).not.2 h0'⟩).1
  · by_cases h0 : w₁ i = 0
    · exact wSameSide_of_left_mem _ ((s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).2 h0)
    · by_cases h0' : w₂ i = 0
      · exact wSameSide_of_right_mem _
          ((s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).2 h0')
      simp only [h0, h0', or_self, or_false] at h
      exact (s.sSameSide_affineSpan_faceOpposite_of_sign_eq hw₁ hw₂ h h0).wSameSide
/-
**Affine.Simplex.wOppSide_affineSpan_faceOpposite_iff** 是 Mathlib 中的一个引理，位于命名空间 
`Affine.Simplex`。
形式化陈述：wOppSide_affineSpan_faceOpposite_iff {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j
, w₁ j = 1) (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (
s.faceOpposite i).points)).WOppSide (Finset.univ.affineCombination R s.points w₁
) (Finset.univ.affineCombination R s.points w₂) ↔ SignType.sign (w₁ i) = -SignTy
pe.sign (w₂ i) ∨ w₁ i = 0 ∨ w₂ i = 0
参数：n + 1；hw₁ : ∑ j, w₁ j = 1；hw₂ : ∑ j, w₂ j = 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Affine.Simplex.sOppSide_affineSpan_faceOpposite_iff`：sOppSide_affineSpan
_faceOpposite_iff {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1) (hw₂ : ∑ j, w
₂ j = 1) {i : Fin (n + 1)} : (affineSpan …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Affine.Simplex.affineCombination_mem_affineSpan_faceOpposite_iff`：affine
Combination_mem_affineSpan_faceOpposite_iff {n : Nat} [NeZero n] {s : Simplex k 
P n} {w : Fin (n + 1) -> k} (hw : ∑ i, w i = 1) {i : F…
· 使用定理 `AffineSubspace.wOppSide_of_left_mem`：wOppSide_of_left_mem {s : AffineSub
space R P} {x : P} (y : P) (hx : x in s) : s.WOppSide x y
· 使用定理 `AffineSubspace.wOppSide_of_right_mem`：wOppSide_of_right_mem {s : AffineS
ubspace R P} (x : P) {y : P} (hy : y in s) : s.WOppSide x y
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `AffineSubspace.SOppSide.wOppSide`：∀ {R : Type u_1} {V : Type u_2} {P : T
ype u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrder
edRing R] [inst_3 : Ad…
· 使用定理 `AffineSubspace.SOppSide.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type 
u_4} [inst : CommRing R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRi
ng R] [inst_3 : Ad…
· 使用引理 `Affine.Simplex.sOppSide_affineSpan_faceOpposite_of_pos_of_neg`：sOppSide_
affineSpan_faceOpposite_of_pos_of_neg {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ 
j = 1) (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} (hs₁…
· 使用定理 `sign_eq_one_iff`：sign_eq_one_iff : sign a = 1 ↔ 0 < a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `sign_eq_neg_one_iff`：sign_eq_neg_one_iff : sign a = -1 ↔ a < 0
（共 32 条，此处仅展示前 30 条）
-/
lemma wOppSide_affineSpan_faceOpposite_iff {w₁ w₂ : Fin (n + 1) → R} (hw₁ : ∑ j, w₁ j = 1)
    (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).WOppSide
      (Finset.univ.affineCombination R s.points w₁)
      (Finset.univ.affineCombination R s.points w₂) ↔
        SignType.sign (w₁ i) = -SignType.sign (w₂ i) ∨ w₁ i = 0 ∨ w₂ i = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_cases h0 : w₁ i = 0
    · simp [h0]
    by_cases h0' : w₂ i = 0
    · simp [h0']
    exact .inl ((s.sOppSide_affineSpan_faceOpposite_iff hw₁ hw₂).1 ⟨h,
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.2 h0,
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).not.2 h0'⟩).1
  · by_cases h0 : w₁ i = 0
    · exact wOppSide_of_left_mem _ ((s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).2 h0)
    · by_cases h0' : w₂ i = 0
      · exact wOppSide_of_right_mem _
          ((s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).2 h0')
      simp only [h0, h0', or_self, or_false] at h
      rcases Ne.lt_or_gt h0 with h' | h'
      · rw [sign_neg h', neg_inj, eq_comm, sign_eq_one_iff] at h
        exact (s.sOppSide_affineSpan_faceOpposite_of_pos_of_neg hw₂ hw₁ h h').symm.wOppSide
      · rw [sign_pos h', eq_comm, neg_eq_iff_eq_neg, sign_eq_neg_one_iff] at h
        exact (s.sOppSide_affineSpan_faceOpposite_of_pos_of_neg hw₁ hw₂ h' h).wOppSide
/-
**Affine.Simplex.sSameSide_affineSpan_faceOpposite_point_left_iff** 是 Mathlib 中的
一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：sSameSide_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) -> R} (h
w : ∑ j, w j = 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.faceOpposite i
).points)).SSameSide (s.points i) (Finset.univ.affineCombination R s.points w) ↔
 0 < w i
参数：n + 1；hw : ∑ j, w j = 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用引理 `Affine.Simplex.sSameSide_affineSpan_faceOpposite_iff`：sSameSide_affineSp
an_faceOpposite_iff {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1) (hw₂ : ∑ j,
 w₂ j = 1) {i : Fin (n + 1)} : (affineSpan…
· 使用定理 `Fintype.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommM
onoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (i : ι) (a : M),   ∑ j, P
i.single i a…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sSameSide_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) → R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SSameSide (s.points i)
      (Finset.univ.affineCombination R s.points w) ↔ 0 < w i := by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i),
    s.sSameSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw, eq_comm]
  simp [sign_eq_one_iff]
/-
**Affine.Simplex.sSameSide_affineSpan_faceOpposite_point_right_iff** 是 Mathlib 中
的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：sSameSide_affineSpan_faceOpposite_point_right_iff {w : Fin (n + 1) -> R} (
hw : ∑ j, w j = 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.faceOpposite 
i).points)).SSameSide (Finset.univ.affineCombination R s.points w) (s.points i) 
↔ 0 < w i
参数：n + 1；hw : ∑ j, w j = 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.sSameSide_comm`：sSameSide_comm {s : AffineSubspace R P} {
x y : P} : s.SSameSide x y ↔ s.SSameSide y x
· 使用引理 `Affine.Simplex.sSameSide_affineSpan_faceOpposite_point_left_iff`：sSameSi
de_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) -> R} (hw : ∑ j, w j 
= 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sSameSide_affineSpan_faceOpposite_point_right_iff {w : Fin (n + 1) → R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SSameSide
      (Finset.univ.affineCombination R s.points w) (s.points i) ↔ 0 < w i := by
  rw [sSameSide_comm, s.sSameSide_affineSpan_faceOpposite_point_left_iff hw]
/-
**Affine.Simplex.sOppSide_affineSpan_faceOpposite_point_left_iff** 是 Mathlib 中的一
个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：sOppSide_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) -> R} (hw
 : ∑ j, w j = 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.faceOpposite i)
.points)).SOppSide (s.points i) (Finset.univ.affineCombination R s.points w) ↔ w
 i < 0
参数：n + 1；hw : ∑ j, w j = 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用引理 `Affine.Simplex.sOppSide_affineSpan_faceOpposite_iff`：sOppSide_affineSpan
_faceOpposite_iff {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1) (hw₂ : ∑ j, w
₂ j = 1) {i : Fin (n + 1)} : (affineSpan …
· 使用定理 `Fintype.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommM
onoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (i : ι) (a : M),   ∑ j, P
i.single i a…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sOppSide_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) → R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SOppSide (s.points i)
      (Finset.univ.affineCombination R s.points w) ↔ w i < 0 := by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i),
    s.sOppSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw, eq_comm,
    neg_eq_iff_eq_neg]
  simp [sign_eq_neg_one_iff]
/-
**Affine.Simplex.sOppSide_affineSpan_faceOpposite_point_right_iff** 是 Mathlib 中的
一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：sOppSide_affineSpan_faceOpposite_point_right_iff {w : Fin (n + 1) -> R} (h
w : ∑ j, w j = 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.faceOpposite i
).points)).SOppSide (Finset.univ.affineCombination R s.points w) (s.points i) ↔ 
w i < 0
参数：n + 1；hw : ∑ j, w j = 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.sOppSide_comm`：sOppSide_comm {s : AffineSubspace R P} {x 
y : P} : s.SOppSide x y ↔ s.SOppSide y x
· 使用引理 `Affine.Simplex.sOppSide_affineSpan_faceOpposite_point_left_iff`：sOppSide
_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) -> R} (hw : ∑ j, w j = 
1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.f…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sOppSide_affineSpan_faceOpposite_point_right_iff {w : Fin (n + 1) → R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SOppSide
      (Finset.univ.affineCombination R s.points w) (s.points i) ↔ w i < 0 := by
  rw [sOppSide_comm, s.sOppSide_affineSpan_faceOpposite_point_left_iff hw]
/-
**Affine.Simplex.wSameSide_affineSpan_faceOpposite_point_left_iff** 是 Mathlib 中的
一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：wSameSide_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) -> R} (h
w : ∑ j, w j = 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.faceOpposite i
).points)).WSameSide (s.points i) (Finset.univ.affineCombination R s.points w) ↔
 0 <= w i
参数：n + 1；hw : ∑ j, w j = 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用引理 `Affine.Simplex.wSameSide_affineSpan_faceOpposite_iff`：wSameSide_affineSp
an_faceOpposite_iff {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1) (hw₂ : ∑ j,
 w₂ j = 1) {i : Fin (n + 1)} : (affineSpan…
· 使用定理 `Fintype.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommM
onoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (i : ι) (a : M),   ∑ j, P
i.single i a…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma wSameSide_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) → R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).WSameSide (s.points i)
      (Finset.univ.affineCombination R s.points w) ↔ 0 ≤ w i := by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i),
    s.wSameSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw, eq_comm]
  simp [sign_eq_one_iff, le_iff_eq_or_lt', or_comm]
/-
**Affine.Simplex.wSameSide_affineSpan_faceOpposite_point_right_iff** 是 Mathlib 中
的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：wSameSide_affineSpan_faceOpposite_point_right_iff {w : Fin (n + 1) -> R} (
hw : ∑ j, w j = 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.faceOpposite 
i).points)).WSameSide (Finset.univ.affineCombination R s.points w) (s.points i) 
↔ 0 <= w i
参数：n + 1；hw : ∑ j, w j = 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.wSameSide_comm`：wSameSide_comm {s : AffineSubspace R P} {
x y : P} : s.WSameSide x y ↔ s.WSameSide y x
· 使用引理 `Affine.Simplex.wSameSide_affineSpan_faceOpposite_point_left_iff`：wSameSi
de_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) -> R} (hw : ∑ j, w j 
= 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma wSameSide_affineSpan_faceOpposite_point_right_iff {w : Fin (n + 1) → R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).WSameSide
      (Finset.univ.affineCombination R s.points w) (s.points i) ↔ 0 ≤ w i := by
  rw [wSameSide_comm, s.wSameSide_affineSpan_faceOpposite_point_left_iff hw]
/-
**Affine.Simplex.wOppSide_affineSpan_faceOpposite_point_left_iff** 是 Mathlib 中的一
个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：wOppSide_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) -> R} (hw
 : ∑ j, w j = 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.faceOpposite i)
.points)).WOppSide (s.points i) (Finset.univ.affineCombination R s.points w) ↔ w
 i <= 0
参数：n + 1；hw : ∑ j, w j = 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用引理 `Affine.Simplex.wOppSide_affineSpan_faceOpposite_iff`：wOppSide_affineSpan
_faceOpposite_iff {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1) (hw₂ : ∑ j, w
₂ j = 1) {i : Fin (n + 1)} : (affineSpan …
· 使用定理 `Fintype.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommM
onoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (i : ι) (a : M),   ∑ j, P
i.single i a…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma wOppSide_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) → R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).WOppSide (s.points i)
      (Finset.univ.affineCombination R s.points w) ↔ w i ≤ 0 := by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i),
    s.wOppSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw, eq_comm,
    neg_eq_iff_eq_neg]
  simp [sign_eq_neg_one_iff, le_iff_eq_or_lt, or_comm]
/-
**Affine.Simplex.wOppSide_affineSpan_faceOpposite_point_right_iff** 是 Mathlib 中的
一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：wOppSide_affineSpan_faceOpposite_point_right_iff {w : Fin (n + 1) -> R} (h
w : ∑ j, w j = 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.faceOpposite i
).points)).WOppSide (Finset.univ.affineCombination R s.points w) (s.points i) ↔ 
w i <= 0
参数：n + 1；hw : ∑ j, w j = 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.wOppSide_comm`：wOppSide_comm {s : AffineSubspace R P} {x 
y : P} : s.WOppSide x y ↔ s.WOppSide y x
· 使用引理 `Affine.Simplex.wOppSide_affineSpan_faceOpposite_point_left_iff`：wOppSide
_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) -> R} (hw : ∑ j, w j = 
1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.f…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma wOppSide_affineSpan_faceOpposite_point_right_iff {w : Fin (n + 1) → R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).WOppSide
      (Finset.univ.affineCombination R s.points w) (s.points i) ↔ w i ≤ 0 := by
  rw [wOppSide_comm, s.wOppSide_affineSpan_faceOpposite_point_left_iff hw]

end Affine.Simplex

