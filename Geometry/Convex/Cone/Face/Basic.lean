/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# Faces of pointed cones

This file defines what it means for a pointed cone to be a face of another pointed cone and
establishes basic properties of this relation.
A subcone `F` of a cone `C` is a face if any two points in `C` that have a positive combination
in `F` are also in `F`.

## Main declarations

* `IsFaceOf F C`: States that the pointed cone `F` is a face of the pointed cone `C`.

## Implementation notes

* We do not use `IsExtreme` as a definition because this is an affine notion and does not allow the
  flexibility necessary to deal with cones over general rings. E.g. the cone of positive integers
  has no proper subset that are extreme. We prove that every face is an extreme set of its cone.
* Most results proven over a division ring hold more generally over an Archimedean ring. In
  particular, `iff_mem_of_add_mem_left` holds whenever for every `x ∈ R` there is a `y ∈ R` with
  `1 ≤ x * y`.

-/

open Submodule

public section

namespace PointedCone

variable {R M N : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

/-- A sub-cone `F` of a pointed cone `C` is a face of `C` if any two points of `C` with a strictly
positive combination in `F` are also in `F`. -/
@[mk_iff]
/-
**PointedCone.IsFaceOf** 是 Mathlib 中的一个归纳类型，位于命名空间 `PointedCone`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     [inst : Semiring R] →       [inst_
1 : PartialOrder R] →         [inst_2 : IsOrderedRing R] →           [inst_3 : A
ddCommGroup M] → [inst_4 : _root_.Module R M] → PointedCone R M → PointedCone R 
M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sub-cone `F` of a pointed cone `C` is a face of `C` if any two points of `C` w
ith a strictly
positive combination in `F` are also in `F`.
-/
structure IsFaceOf (F C : PointedCone R M) : Prop where
  le : F ≤ C
  mem_of_smul_add_mem {x y : M} {a : R} :
    x ∈ C → y ∈ C → 0 < a → a • x + y ∈ F → x ∈ F

variable {C C₁ C₂ F F₁ F₂ : PointedCone R M}

namespace IsFaceOf

/-
**PointedCone.IsFaceOf.mem_of_smul_add_smul_mem_left** 是 Mathlib 中的一个定理，位于命名空间 `
PointedCone.IsFaceOf`。
形式化陈述：mem_of_smul_add_smul_mem_left {x y : M} {a b : R} (hF : F.IsFaceOf C) (hx 
: x in C) (hy : y in C) (ha : 0 < a) (hb : 0 < b) (h : a • x + b • y in F) : x i
n F
参数：hF : F.IsFaceOf C；hx : x in C；hy : y in C；ha : 0 < a；hb : 0 < b；h : a • x + b
 • y in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.mem_of_smul_add_mem`：∀ {R : Type u_1} {M : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [in
st_3 : AddCommGroup M] [inst_4…
· 使用定理 `PointedCone.smul_mem`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R
] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid
 E] [inst_…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem mem_of_smul_add_smul_mem_left {x y : M} {a b : R} (hF : F.IsFaceOf C) (hx : x ∈ C)
    (hy : y ∈ C) (ha : 0 < a) (hb : 0 < b) (h : a • x + b • y ∈ F) : x ∈ F :=
  hF.2 hx (smul_mem _ hb.le hy) ha h
/-
**PointedCone.IsFaceOf.mem_of_smul_add_smul_mem_right** 是 Mathlib 中的一个定理，位于命名空间 
`PointedCone.IsFaceOf`。
形式化陈述：mem_of_smul_add_smul_mem_right {x y : M} {a b : R} (hF : F.IsFaceOf C) (hx
 : x in C) (hy : y in C) (ha : 0 < a) (hb : 0 < b) (h : a • x + b • y in F) : y 
in F
参数：hF : F.IsFaceOf C；hx : x in C；hy : y in C；ha : 0 < a；hb : 0 < b；h : a • x + b
 • y in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.mem_of_smul_add_mem`：∀ {R : Type u_1} {M : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [in
st_3 : AddCommGroup M] [inst_4…
· 使用定理 `PointedCone.smul_mem`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R
] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid
 E] [inst_…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem mem_of_smul_add_smul_mem_right {x y : M} {a b : R} (hF : F.IsFaceOf C) (hx : x ∈ C)
    (hy : y ∈ C) (ha : 0 < a) (hb : 0 < b) (h : a • x + b • y ∈ F) : y ∈ F := by
  apply hF.2 hy (smul_mem _ ha.le hx) hb; rwa [add_comm]

/-- A pointed cone `C` is a face of itself. -/
@[refl, simp]
/-
**PointedCone.IsFaceOf.refl** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsFaceOf`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_4 : _root_.Modu
le R M] (C : PointedCone R M), C.IsFaceOf C
参数：C : PointedCone R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
A pointed cone `C` is a face of itself.
-/
protected theorem refl (C : PointedCone R M) : C.IsFaceOf C := ⟨fun _ a ↦ a, fun hx _ _ _ ↦ hx⟩
/-
**PointedCone.IsFaceOf.rfl** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsFaceOf`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_4 : _root_.Modu
le R M] {C : PointedCone R M}, C.IsFaceOf C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PointedCone.IsFaceOf.refl`：∀ {R : Type u_1} {M : Type u_2} [inst : Semir
ing R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommG
roup M] [inst_4…
-/
protected theorem rfl {C : PointedCone R M} : C.IsFaceOf C := .refl _

/-- A face of a cone is a face of another if and only if they are contained in each other. -/
/-
**PointedCone.IsFaceOf.isFaceOf_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.Is
FaceOf`。
形式化陈述：isFaceOf_iff_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : F₁.IsFaceOf F₂
 ↔ F₁ <= F₂
参数：h₁ : F₁.IsFaceOf C；h₂ : F₂.IsFaceOf C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.le`：∀ {R : Type u_1} {M : Type u_2} [inst : Semirin
g R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGro
up M] [inst_4…
· 使用定理 `PointedCone.IsFaceOf.mem_of_smul_add_mem`：∀ {R : Type u_1} {M : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [in
st_3 : AddCommGroup M] [inst_4…

--- 原说明 ---
A face of a cone is a face of another if and only if they are contained in each 
other.
-/
theorem isFaceOf_iff_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    F₁.IsFaceOf F₂ ↔ F₁ ≤ F₂ :=
  ⟨IsFaceOf.le, fun h ↦ ⟨h, fun hx hy ha hxy ↦ h₁.2 (h₂.le hx) (h₂.le hy) ha hxy⟩⟩

/-- A face of a cone is an extreme subset of the cone. -/
/-
**PointedCone.IsFaceOf.isExtreme** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsFaceOf
`。
形式化陈述：isExtreme (h : F.IsFaceOf C) : IsExtreme R (C : Set M) F
参数：h : F.IsFaceOf C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.le`：∀ {R : Type u_1} {M : Type u_2} [inst : Semirin
g R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGro
up M] [inst_4…
· 使用定理 `PointedCone.IsFaceOf.mem_of_smul_add_smul_mem_left`：mem_of_smul_add_smul
_mem_left {x y : M} {a b : R} (hF : F.IsFaceOf C) (hx : x in C) (hy : y in C) (h
a : 0 < a) (hb : 0 < b) (h : a • x + b •…

--- 原说明 ---
A face of a cone is an extreme subset of the cone.
-/
theorem isExtreme (h : F.IsFaceOf C) : IsExtreme R (C : Set M) F := by
  refine ⟨h.1, ?_⟩
  rintro _ xc _ yc _ zf ⟨_, _, a0, b0, -, rfl⟩
  exact h.mem_of_smul_add_smul_mem_left xc yc a0 b0 zf

/-- The intersection of two faces of two cones is a face of the intersection of the cones. -/
/-
**PointedCone.IsFaceOf.inf** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsFaceOf`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_4 : _root_.Modu
le R M] {C₁ C₂ F₁ F₂ : PointedCone R M},   F₁.IsFaceOf C₁ → F₂.IsFaceOf C₂ → (F₁
 ⊓ F₂).IsFaceOf (C₁ ⊓ C₂)
参数：F₁ ⊓ F₂；C₁ ⊓ C₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `PointedCone.IsFaceOf.le`：∀ {R : Type u_1} {M : Type u_2} [inst : Semirin
g R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGro
up M] [inst_4…
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PointedCone.IsFaceOf.mem_of_smul_add_mem`：∀ {R : Type u_1} {M : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [in
st_3 : AddCommGroup M] [inst_4…

--- 原说明 ---
The intersection of two faces of two cones is a face of the intersection of the 
cones.
-/
protected theorem inf (h₁ : F₁.IsFaceOf C₁) (h₂ : F₂.IsFaceOf C₂) :
    (F₁ ⊓ F₂).IsFaceOf (C₁ ⊓ C₂) := by
  use le_inf_iff.mpr ⟨Set.inter_subset_left.trans h₁.le, Set.inter_subset_right.trans h₂.le⟩
  simp only [mem_inf, and_imp]
  refine fun xc₁ xc₂ yc₁ yc₂ a0 hz₁ hz₂ ↦ ⟨?_, ?_⟩
  · exact h₁.mem_of_smul_add_mem xc₁ yc₁ a0 hz₁
  · exact h₂.mem_of_smul_add_mem xc₂ yc₂ a0 hz₂

/-- The intersection of two faces of a cone is a face of the cone. -/
/-
**PointedCone.IsFaceOf.inf_left** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsFaceOf`
。
形式化陈述：inf_left (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : (F₁ ⊓ F₂).IsFaceOf C
参数：h₁ : F₁.IsFaceOf C；h₂ : F₂.IsFaceOf C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.inf`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiri
ng R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGr
oup M] [inst_4…
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a

--- 原说明 ---
The intersection of two faces of a cone is a face of the cone.
-/
theorem inf_left (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : (F₁ ⊓ F₂).IsFaceOf C :=
  inf_idem C ▸ IsFaceOf.inf h₁ h₂

/-- If a cone is a face of two cones simultaneously, then it's also a face of their intersection. -/
/-
**PointedCone.IsFaceOf.inf_right** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsFaceOf
`。
形式化陈述：inf_right (h₁ : F.IsFaceOf C₁) (h₂ : F.IsFaceOf C₂) : F.IsFaceOf (C₁ ⊓ C₂)
参数：h₁ : F.IsFaceOf C₁；h₂ : F.IsFaceOf C₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.inf`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiri
ng R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGr
oup M] [inst_4…
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a

--- 原说明 ---
If a cone is a face of two cones simultaneously, then it's also a face of their 
intersection.
-/
theorem inf_right (h₁ : F.IsFaceOf C₁) (h₂ : F.IsFaceOf C₂) : F.IsFaceOf (C₁ ⊓ C₂) :=
  inf_idem F ▸ IsFaceOf.inf h₁ h₂
/-
**PointedCone.IsFaceOf.sInf** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsFaceOf`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_4 : _root_.Modu
le R M] {C : PointedCone R M} (F : Set (PointedCone R M)),   (∀ f ∈ F, f.IsFaceO
f C) → (C ⊓ sInf F).IsFaceOf C
参数：F : Set (PointedCone R M)；∀ f ∈ F, f.IsFaceOf C；C ⊓ sInf F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `PointedCone.IsFaceOf.mem_of_smul_add_mem`：∀ {R : Type u_1} {M : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [in
st_3 : AddCommGroup M] [inst_4…
-/
protected theorem sInf (F : Set (PointedCone R M)) (h : ∀ f ∈ F, f.IsFaceOf C) :
    (C ⊓ sInf F).IsFaceOf C where
  le _ sm := sm.1
  mem_of_smul_add_mem := by
    simp only [mem_inf, mem_sInf, and_imp]
    intro _ _ a xc yc a0 _ h'
    simpa [xc] using fun F Fs ↦ (h F Fs).mem_of_smul_add_mem xc yc a0 (h' F Fs)
/-
**PointedCone.IsFaceOf.mem_of_add_mem_left** 是 Mathlib 中的一个定理，位于命名空间 `PointedCon
e.IsFaceOf`。
形式化陈述：mem_of_add_mem_left (hF : F.IsFaceOf C) {x y : M} (hx : x in C) (hy : y in
 C) (hxy : x + y in F) : x in F
参数：hF : F.IsFaceOf C；hx : x in C；hy : y in C；hxy : x + y in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `PointedCone.IsFaceOf.mem_of_smul_add_mem`：∀ {R : Type u_1} {M : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [in
st_3 : AddCommGroup M] [inst_4…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
-/
theorem mem_of_add_mem_left (hF : F.IsFaceOf C) {x y : M}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x + y ∈ F) : x ∈ F := by
  nontriviality R using Module.subsingleton R M
  simpa [hxy] using hF.mem_of_smul_add_mem hx hy zero_lt_one
/-
**PointedCone.IsFaceOf.mem_of_add_mem_right** 是 Mathlib 中的一个定理，位于命名空间 `PointedCo
ne.IsFaceOf`。
形式化陈述：mem_of_add_mem_right (hF : F.IsFaceOf C) {x y : M} (hx : x in C) (hy : y i
n C) (hxy : x + y in F) : y in F
参数：hF : F.IsFaceOf C；hx : x in C；hy : y in C；hxy : x + y in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.mem_of_add_mem_left`：mem_of_add_mem_left (hF : F.Is
FaceOf C) {x y : M} (hx : x in C) (hy : y in C) (hxy : x + y in F) : x in F
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem mem_of_add_mem_right (hF : F.IsFaceOf C) {x y : M}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x + y ∈ F) : y ∈ F := by
  rw [add_comm x y] at hxy; exact mem_of_add_mem_left hF hy hx hxy
/-
**PointedCone.IsFaceOf.add_mem_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.Is
FaceOf`。
形式化陈述：add_mem_iff_mem (hF : F.IsFaceOf C) {x y : M} (hx : x in C) (hy : y in C) 
: x + y in F ↔ x in F ∧ y in F
参数：hF : F.IsFaceOf C；hx : x in C；hy : y in C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.mem_of_add_mem_left`：mem_of_add_mem_left (hF : F.Is
FaceOf C) {x y : M} (hx : x in C) (hy : y in C) (hxy : x + y in F) : x in F
· 使用定理 `PointedCone.IsFaceOf.mem_of_add_mem_right`：mem_of_add_mem_right (hF : F.
IsFaceOf C) {x y : M} (hx : x in C) (hy : y in C) (hxy : x + y in F) : y in F
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
-/
theorem add_mem_iff_mem (hF : F.IsFaceOf C) {x y : M} (hx : x ∈ C) (hy : y ∈ C) :
    x + y ∈ F ↔ x ∈ F ∧ y ∈ F := by
  refine ⟨?_, fun ⟨hx, hy⟩ ↦ F.add_mem hx hy⟩
  exact fun h ↦ ⟨mem_of_add_mem_left hF hx hy h, mem_of_add_mem_right hF hx hy h⟩

/-- If the sum of points of a cone is in a face, then all the points are in the face. -/
/-
**PointedCone.IsFaceOf.mem_of_sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsF
aceOf`。
形式化陈述：mem_of_sum_mem {ι : Type*} [Fintype ι] {f : ι -> M} (hF : F.IsFaceOf C) (h
sC : forall i : ι, f i in C) (hs : ∑ i : ι, f i in F) (i : ι) : f i in F
参数：hF : F.IsFaceOf C；hsC : forall i : ι, f i in C；hs : ∑ i : ι, f i in F；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.mem_of_add_mem_left`：mem_of_add_mem_left (hF : F.Is
FaceOf C) {x y : M} (hx : x in C) (hy : y in C) (hxy : x + y in F) : x in F
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_erase_eq_sub`：∀ {ι : Type u_1} {G : Type u_3} {s : Finset ι} 
[inst : AddCommGroup G] [inst_1 : DecidableEq ι] {f : ι → G} {a : ι},   a ∈ s → 
∑ x ∈ s.erase…
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
If the sum of points of a cone is in a face, then all the points are in the face
.
-/
theorem mem_of_sum_mem {ι : Type*} [Fintype ι] {f : ι → M} (hF : F.IsFaceOf C)
    (hsC : ∀ i : ι, f i ∈ C) (hs : ∑ i : ι, f i ∈ F) (i : ι) : f i ∈ F := by classical
  apply hF.mem_of_add_mem_left (hsC i) (sum_mem (fun j (_ : j ∈ Finset.univ.erase i) ↦ hsC j))
  simp [hs]
/-
**PointedCone.IsFaceOf.sum_mem_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.Is
FaceOf`。
形式化陈述：sum_mem_iff_mem {ι : Type*} [Fintype ι] {f : ι -> M} (hF : F.IsFaceOf C) (
hsC : forall i, f i in C) : ∑ i, f i in F ↔ forall i, f i in F
参数：hF : F.IsFaceOf C；hsC : forall i, f i in C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.mem_of_sum_mem`：mem_of_sum_mem {ι : Type*} [Fintype
 ι] {f : ι -> M} (hF : F.IsFaceOf C) (hsC : forall i : ι, f i in C) (hs : ∑ i : 
ι, f i in F) (i : ι) : f …
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
-/
theorem sum_mem_iff_mem {ι : Type*} [Fintype ι] {f : ι → M} (hF : F.IsFaceOf C)
    (hsC : ∀ i, f i ∈ C) : ∑ i, f i ∈ F ↔ ∀ i, f i ∈ F :=
  ⟨mem_of_sum_mem hF hsC, fun a ↦ Submodule.sum_mem F fun c _ ↦ a c⟩

/-- If the positive combination of points of a cone is in a face, then all the points are
in the face. -/
/-
**PointedCone.IsFaceOf.mem_of_sum_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `PointedCon
e.IsFaceOf`。
形式化陈述：mem_of_sum_smul_mem {ι : Type*} [Fintype ι] {f : ι -> M} {c : ι -> R} (hF 
: F.IsFaceOf C) (hsC : forall i : ι, f i in C) (hc : forall i, 0 <= c i) (hs : ∑
 i : ι, c i • f i in F) (i : ι) (hci : 0 < c i) : f i in F
参数：hF : F.IsFaceOf C；hsC : forall i : ι, f i in C；hc : forall i, 0 <= c i；hs : ∑
 i : ι, c i • f i in F；i : ι；hci : 0 < c i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.mem_of_smul_add_mem`：∀ {R : Type u_1} {M : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [in
st_3 : AddCommGroup M] [inst_4…
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `PointedCone.smul_mem`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R
] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid
 E] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_eq_add_sum_sdiff_singleton`：∀ {ι : Type u_1} {M : Type u_3} [
inst : AddCommMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} (i : ι) (f : ι →
 M),   (i ∉ s → f i = 0) → …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
If the positive combination of points of a cone is in a face, then all the point
s are
in the face.
-/
theorem mem_of_sum_smul_mem {ι : Type*} [Fintype ι] {f : ι → M} {c : ι → R}
    (hF : F.IsFaceOf C) (hsC : ∀ i : ι, f i ∈ C) (hc : ∀ i, 0 ≤ c i) (hs : ∑ i : ι, c i • f i ∈ F)
    (i : ι) (hci : 0 < c i) : f i ∈ F := by classical
  rw [Finset.sum_eq_add_sum_sdiff_singleton i] at hs
  · refine hF.mem_of_smul_add_mem (hsC i) ?_ hci hs
    exact C.sum_mem fun i _ ↦ C.smul_mem (hc i) (hsC i)
  · simp

/-- The face of a face of a cone is also a face of the cone. -/
@[trans]
/-
**PointedCone.IsFaceOf.trans** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsFaceOf`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_4 : _root_.Modu
le R M] {C F₁ F₂ : PointedCone R M},   F₂.IsFaceOf F₁ → F₁.IsFaceOf C → F₂.IsFac
eOf C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.le`：∀ {R : Type u_1} {M : Type u_2} [inst : Semirin
g R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGro
up M] [inst_4…
· 使用定理 `PointedCone.IsFaceOf.mem_of_smul_add_mem`：∀ {R : Type u_1} {M : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [in
st_3 : AddCommGroup M] [inst_4…
· 使用定理 `PointedCone.IsFaceOf.mem_of_add_mem_right`：mem_of_add_mem_right (hF : F.
IsFaceOf C) {x y : M} (hx : x in C) (hy : y in C) (hxy : x + y in F) : y in F
· 使用定理 `PointedCone.smul_mem`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R
] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid
 E] [inst_…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
The face of a face of a cone is also a face of the cone.
-/
protected theorem trans (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf C) : F₂.IsFaceOf C := by
  refine ⟨h₁.1.trans h₂.1, fun hx hy ha hxy ↦ h₁.2 (h₂.2 hx hy ha (h₁.le hxy)) ?_ ha hxy⟩
  exact h₂.mem_of_add_mem_right (smul_mem _ ha.le hx) hy (h₁.le hxy)

section Map

variable [AddCommGroup N] [Module R N]

/-- The image of a face of a cone under an injective linear map is a face of the
image of the cone. -/
/-
**PointedCone.IsFaceOf.map** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsFaceOf`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Semiring R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_
4 : _root_.Module R M] {C F : PointedCone R M} [inst_5 : AddCommGroup N]   [inst
_6 : _root_.Module R N] (f : M →ₗ[R] N),   Function.Injective ⇑f → F.IsFaceOf C 
→ (PointedCone.map f F).IsFaceOf (PointedCone.map f C)
参数：f : M →ₗ[R] N；PointedCone.map f F；PointedCone.map f C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_mono`：map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M}
 : p <= p' -> map f p <= map f p'
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.le`：∀ {R : Type u_1} {M : Type u_2} [inst : Semirin
g R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGro
up M] [inst_4…
· 使用定理 `PointedCone.IsFaceOf.mem_of_smul_add_mem`：∀ {R : Type u_1} {M : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [in
st_3 : AddCommGroup M] [inst_4…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…

--- 原说明 ---
The image of a face of a cone under an injective linear map is a face of the
image of the cone.
-/
protected theorem map (f : M →ₗ[R] N) (hf : Function.Injective f) (hF : F.IsFaceOf C) :
    (F.map f).IsFaceOf (C.map f) where
  le := map_mono hF.le
  mem_of_smul_add_mem := by
    rintro _ _ a ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ha ⟨z, hz₁, hz₂⟩
    dsimp at hz₂
    rw [← map_smul, ← map_add] at hz₂
    exact ⟨x, hF.mem_of_smul_add_mem hx hy ha (hf hz₂ ▸ hz₁), rfl⟩

/-- The image of a face of a cone under an equivalence is a face of the image of the cone. -/
/-
**PointedCone.IsFaceOf.map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsFaceOf
`。
形式化陈述：map_equiv (e : M ≃ₗ[R] N) (hF : F.IsFaceOf C) : (F.map (e : M ->ₗ[R] N)).I
sFaceOf (C.map e)
参数：e : M ≃ₗ[R] N；hF : F.IsFaceOf C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PointedCone.IsFaceOf.map`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3}
 [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [ins
t_3 : AddCommG…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
The image of a face of a cone under an equivalence is a face of the image of the
 cone.
-/
theorem map_equiv (e : M ≃ₗ[R] N) (hF : F.IsFaceOf C) :
    (F.map (e : M →ₗ[R] N)).IsFaceOf (C.map e) := hF.map _ e.injective
/-
**PointedCone.IsFaceOf.of_map_injective** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.I
sFaceOf`。
形式化陈述：of_map_injective {f : M ->ₗ[R] N} (hf : Function.Injective f) (hc : (map f
 F).IsFaceOf (map f C)) : F.IsFaceOf C
参数：hf : Function.Injective f；hc : (map f F).IsFaceOf (map f C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PointedCone.mem_map`：mem_map {f : E ->ₗ[R] F} {C : PointedCone R E} {y :
 F} : y in C.map f ↔ exists x in C, f x = y
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem of_map_injective {f : M →ₗ[R] N} (hf : Function.Injective f)
    (hc : (map f F).IsFaceOf (map f C)) : F.IsFaceOf C := by
  obtain ⟨sub, hF⟩ := hc
  refine ⟨fun x xf ↦ ?_, fun hx hy ha h ↦ ?_⟩
  · obtain ⟨y, yC, hy⟩ := mem_map.mp <| sub (mem_map_of_mem xf)
    rwa [hf hy] at yC
  · simp only [mem_map, forall_exists_index, and_imp] at hF
    obtain ⟨_, ⟨hx', hhx'⟩⟩ := hF _ hx rfl _ hy rfl ha _ h (by simp)
    convert hx'
    exact hf hhx'.symm

/-- The comap of a face of a cone under a linear map is a face of the comap of the cone. -/
/-
**PointedCone.IsFaceOf.comap** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsFaceOf`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Semiring R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGroup M] [inst_
4 : _root_.Module R M] {C F : PointedCone R M} [inst_5 : AddCommGroup N]   [inst
_6 : _root_.Module R N] (f : N →ₗ[R] M), F.IsFaceOf C → (PointedCone.comap f F).
IsFaceOf (PointedCone.comap f C)
参数：f : N →ₗ[R] M；PointedCone.comap f F；PointedCone.comap f C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.le`：∀ {R : Type u_1} {M : Type u_2} [inst : Semirin
g R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGro
up M] [inst_4…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `PointedCone.IsFaceOf.mem_of_smul_add_mem`：∀ {R : Type u_1} {M : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [in
st_3 : AddCommGroup M] [inst_4…

--- 原说明 ---
The comap of a face of a cone under a linear map is a face of the comap of the c
one.
-/
protected theorem comap (f : N →ₗ[R] M) (hF : F.IsFaceOf C) : (F.comap f).IsFaceOf (C.comap f) := by
  refine ⟨comap_mono hF.le, ?_⟩
  simp only [mem_comap, map_add, map_smul]
  exact hF.mem_of_smul_add_mem
/-
**PointedCone.IsFaceOf.of_comap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `PointedCon
e.IsFaceOf`。
形式化陈述：of_comap_surjective {f : N ->ₗ[R] M} (hf : Function.Surjective f) (hc : (F
.comap f).IsFaceOf (C.comap f)) : F.IsFaceOf C
参数：hf : Function.Surjective f；hc : (F.comap f).IsFaceOf (C.comap f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PointedCone.mem_comap`：mem_comap {f : E ->ₗ[R] F} {C : PointedCone R F} 
{x : E} : x in C.comap f ↔ f x in C
· 使用定理 `PointedCone.IsFaceOf.le`：∀ {R : Type u_1} {M : Type u_2} [inst : Semirin
g R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGro
up M] [inst_4…
· 使用定理 `PointedCone.IsFaceOf.mem_of_smul_add_mem`：∀ {R : Type u_1} {M : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [in
st_3 : AddCommGroup M] [inst_4…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
theorem of_comap_surjective {f : N →ₗ[R] M} (hf : Function.Surjective f)
    (hc : (F.comap f).IsFaceOf (C.comap f)) : F.IsFaceOf C := by
  refine ⟨fun x xF ↦ ?_, fun {x y _} xC yC a0 h ↦ ?_⟩
  · rw [← (hf x).choose_spec] at xF ⊢
    exact mem_comap.mp (hc.1 xF)
  · rw [← (hf x).choose_spec] at h ⊢ xC
    rw [← (hf y).choose_spec] at h yC
    exact hc.2 xC yC a0 (by simpa)

end Map

end IsFaceOf

/-- The image of a cone `F` under an injective linear map is a face of the
image of another cone `C` if and only if `F` is a face of `C`. -/
/-
**PointedCone.isFaceOf_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：isFaceOf_map_iff [AddCommGroup N] [Module R N] {f : M ->ₗ[R] N} (hf : Func
tion.Injective f) : (F.map f).IsFaceOf (C.map f) ↔ F.IsFaceOf C
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PointedCone.IsFaceOf.of_map_injective`：of_map_injective {f : M ->ₗ[R] N}
 (hf : Function.Injective f) (hc : (map f F).IsFaceOf (map f C)) : F.IsFaceOf C
· 使用定理 `PointedCone.IsFaceOf.map`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3}
 [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [ins
t_3 : AddCommG…

--- 原说明 ---
The image of a cone `F` under an injective linear map is a face of the
image of another cone `C` if and only if `F` is a face of `C`.
-/
theorem isFaceOf_map_iff [AddCommGroup N] [Module R N] {f : M →ₗ[R] N} (hf : Function.Injective f) :
    (F.map f).IsFaceOf (C.map f) ↔ F.IsFaceOf C :=
  ⟨IsFaceOf.of_map_injective hf, IsFaceOf.map _ hf⟩

/-- The comap of a cone `F` under a surjective linear map is a face of the
comap of another cone `F` if and only if `F` is a face of `C`. -/
/-
**PointedCone.isFaceOf_comap_iff** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：isFaceOf_comap_iff [AddCommGroup N] [Module R N] {f : N ->ₗ[R] M} (hf : Fu
nction.Surjective f) : (F.comap f).IsFaceOf (C.comap f) ↔ F.IsFaceOf C
参数：hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PointedCone.IsFaceOf.of_comap_surjective`：of_comap_surjective {f : N ->ₗ
[R] M} (hf : Function.Surjective f) (hc : (F.comap f).IsFaceOf (C.comap f)) : F.
IsFaceOf C
· 使用定理 `PointedCone.IsFaceOf.comap`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_
3} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [i
nst_3 : AddCommG…

--- 原说明 ---
The comap of a cone `F` under a surjective linear map is a face of the
comap of another cone `F` if and only if `F` is a face of `C`.
-/
theorem isFaceOf_comap_iff [AddCommGroup N] [Module R N] {f : N →ₗ[R] M}
    (hf : Function.Surjective f) : (F.comap f).IsFaceOf (C.comap f) ↔ F.IsFaceOf C :=
  ⟨IsFaceOf.of_comap_surjective hf, IsFaceOf.comap _⟩

end Semiring

section DivisionRing

variable [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable {C F F₁ F₂ : PointedCone R M}

namespace IsFaceOf

/-
**PointedCone.IsFaceOf.of_mem_of_add_mem_left** 是 Mathlib 中的一个定理，位于命名空间 `Pointed
Cone.IsFaceOf`。
形式化陈述：of_mem_of_add_mem_left (h₁ : F <= C) (h₂ : forall {x y : M}, x in C -> y i
n C -> x + y in F -> x in F) : F.IsFaceOf C
参数：h₁ : F <= C；h₂ : forall {x y : M}, x in C -> y in C -> x + y in F -> x in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `PointedCone.smul_mem`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R
] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid
 E] [inst_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem of_mem_of_add_mem_left (h₁ : F ≤ C) (h₂ : ∀ {x y : M}, x ∈ C → y ∈ C → x + y ∈ F → x ∈ F) :
    F.IsFaceOf C := by
  refine ⟨h₁, fun hx hy ha haxy ↦ ?_⟩
  simpa [← smul_assoc, inv_mul_cancel₀ (ne_of_gt ha)] using smul_mem _
    (inv_nonneg.mpr (le_of_lt ha)) <| h₂ (smul_mem _ (le_of_lt ha) hx) hy haxy

/-- The lineality space of a cone is a face. -/
/-
**PointedCone.IsFaceOf.lineal** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone.IsFaceOf`。
形式化陈述：lineal (C : PointedCone R M) : IsFaceOf C.lineal C
参数：C : PointedCone R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PointedCone.IsFaceOf.of_mem_of_add_mem_left`：of_mem_of_add_mem_left (h₁ 
: F <= C) (h₂ : forall {x y : M}, x in C -> y in C -> x + y in F -> x in F) : F.
IsFaceOf C
· 使用引理 `PointedCone.lineal_le`：lineal_le (C : PointedCone R E) : C.lineal <= C
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `neg_add_cancel_comm`：∀ {G : Type u_1} [inst : AddCommGroup G] (a b : G),
 -a + b + a = b
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a

--- 原说明 ---
The lineality space of a cone is a face.
-/
lemma lineal (C : PointedCone R M) : IsFaceOf C.lineal C := by
  apply of_mem_of_add_mem_left (lineal_le C)
  intro _ _ xc yc xyf
  simp [neg_add_rev, xc, true_and] at xyf ⊢
  simpa [neg_add_cancel_comm] using add_mem xyf.2 yc

/-- The lineality space of a cone lies in every face. -/
/-
**PointedCone.IsFaceOf.lineal_le** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone.IsFaceOf
`。
形式化陈述：lineal_le (hF : F.IsFaceOf C) : C.lineal <= F
参数：hF : F.IsFaceOf C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.mem_of_add_mem_left`：mem_of_add_mem_left (hF : F.Is
FaceOf C) {x y : M} (hx : x in C) (hy : y in C) (hxy : x + y in F) : x in F
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M

--- 原说明 ---
The lineality space of a cone lies in every face.
-/
lemma lineal_le (hF : F.IsFaceOf C) : C.lineal ≤ F :=
  fun _ hx ↦ hF.mem_of_add_mem_left hx.1 hx.2 (by simp)

/-- The lineality space of a face of a cone agrees with the lineality space of the cone. -/
/-
**PointedCone.IsFaceOf.lineal_congr** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone.IsFac
eOf`。
形式化陈述：lineal_congr (hF : F.IsFaceOf C) : F.lineal = C.lineal
参数：hF : F.IsFaceOf C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `PointedCone.IsFaceOf.le`：∀ {R : Type u_1} {M : Type u_2} [inst : Semirin
g R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGro
up M] [inst_4…
· 使用定理 `PointedCone.IsFaceOf.mem_of_add_mem_left`：mem_of_add_mem_left (hF : F.Is
FaceOf C) {x y : M} (hx : x in C) (hy : y in C) (hxy : x + y in F) : x in F
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0

--- 原说明 ---
The lineality space of a face of a cone agrees with the lineality space of the c
one.
-/
lemma lineal_congr (hF : F.IsFaceOf C) : F.lineal = C.lineal := by
  ext
  refine ⟨fun ⟨hx, hx'⟩ ↦ ⟨hF.le hx, hF.le hx'⟩, fun ⟨hx, hx'⟩ ↦ ⟨?_, ?_⟩⟩
  · exact hF.mem_of_add_mem_left hx hx' (by simp)
  · exact hF.mem_of_add_mem_left hx' hx (by simp)

section Prod

variable [AddCommGroup N] [Module R N]

/-- The product of two faces of two cones is a face of the product of the cones. -/
/-
**PointedCone.IsFaceOf.prod** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsFaceOf`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : DivisionRing R] [in
st_1 : LinearOrder R]   [inst_2 : IsOrderedRing R] [inst_3 : AddCommGroup M] [in
st_4 : _root_.Module R M] [inst_5 : AddCommGroup N]   [inst_6 : _root_.Module R 
N] {C₁ F₁ : PointedCone R M} {C₂ F₂ : PointedCone R N},   F₁.IsFaceOf C₁ → F₂.Is
FaceOf C₂ → PointedCone.IsFaceOf (Submodule.prod F₁ F₂) (Submodule.prod C₁ C₂)
参数：Submodule.prod F₁ F₂；Submodule.prod C₁ C₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.le`：∀ {R : Type u_1} {M : Type u_2} [inst : Semirin
g R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGro
up M] [inst_4…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PointedCone.IsFaceOf.mem_of_smul_add_mem`：∀ {R : Type u_1} {M : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [in
st_3 : AddCommGroup M] [inst_4…

--- 原说明 ---
The product of two faces of two cones is a face of the product of the cones.
-/
protected theorem prod {C₁ F₁ : PointedCone R M} {C₂ F₂ : PointedCone R N}
    (hF₁ : F₁.IsFaceOf C₁) (hF₂ : F₂.IsFaceOf C₂) : IsFaceOf (F₁.prod F₂) (C₁.prod C₂) := by
  refine ⟨fun x hx ↦ by simpa [mem_prod] using ⟨hF₁.le hx.1, hF₂.le hx.2⟩, ?_⟩
  simp only [mem_prod, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
    Prod.smul_snd, and_imp, Prod.forall]
  intro _ _ _ _ _ xc₁ xc₂ yc₁ yc₂ a0 hab₁ hab₂
  exact ⟨hF₁.mem_of_smul_add_mem xc₁ yc₁ a0 hab₁, hF₂.mem_of_smul_add_mem xc₂ yc₂ a0 hab₂⟩

/-- The projection of a face of a product cone onto the first component is a face of the
projection of the product cone onto the first component. -/
/-
**PointedCone.IsFaceOf.fst** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsFaceOf`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : DivisionRing R] [in
st_1 : LinearOrder R]   [inst_2 : IsOrderedRing R] [inst_3 : AddCommGroup M] [in
st_4 : _root_.Module R M] [inst_5 : AddCommGroup N]   [inst_6 : _root_.Module R 
N] {C₁ : PointedCone R M} {C₂ : PointedCone R N} {F : PointedCone R (M × N)},   
F.IsFaceOf (Submodule.prod C₁ C₂) → (PointedCone.map (LinearMap.fst R M N) F).Is
FaceOf C₁
参数：M × N；Submodule.prod C₁ C₂；PointedCone.map (LinearMap.fst R M N) F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_prod`：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
· 使用定理 `PointedCone.IsFaceOf.le`：∀ {R : Type u_1} {M : Type u_2} [inst : Semirin
g R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommGro
up M] [inst_4…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PointedCone.IsFaceOf.mem_of_smul_add_mem`：∀ {R : Type u_1} {M : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [in
st_3 : AddCommGroup M] [inst_4…
· 使用定理 `Submodule.mem_prod`：mem_prod {p : Submodule R M} {q : Submodule R M'} {x
 : M × M'} : x in prod p q ↔ x.1 in p ∧ x.2 in q
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
The projection of a face of a product cone onto the first component is a face of
 the
projection of the product cone onto the first component.
-/
protected theorem fst {C₁ : PointedCone R M} {C₂ : PointedCone R N}
    {F : PointedCone R (M × N)}
    (hF : F.IsFaceOf (C₁.prod C₂)) : (F.map (.fst R M N)).IsFaceOf C₁ := by
  constructor
  · intro x hx
    simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right] at hx
    exact (Set.mem_prod.mp <| hF.le hx.choose_spec).1
  · simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right,
      forall_exists_index]
    intro x y a hx hy ha z h
    refine ⟨0, hF.mem_of_smul_add_mem (x := (x, 0)) (y := (y, z)) ?_ ?_ ha (by simpa)⟩
    · exact mem_prod.mp ⟨hx, zero_mem C₂⟩
    · exact mem_prod.mp ⟨hy, (hF.le h).2⟩

/-- The projection of a face of a product cone onto the second component is a face of the
projection of the product cone onto the second component. -/
/-
**PointedCone.IsFaceOf.snd** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsFaceOf`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : DivisionRing R] [in
st_1 : LinearOrder R]   [inst_2 : IsOrderedRing R] [inst_3 : AddCommGroup M] [in
st_4 : _root_.Module R M] [inst_5 : AddCommGroup N]   [inst_6 : _root_.Module R 
N] {C₁ : PointedCone R M} {C₂ : PointedCone R N} {F : PointedCone R (M × N)},   
F.IsFaceOf (Submodule.prod C₁ C₂) → (PointedCone.map (LinearMap.snd R M N) F).Is
FaceOf C₂
参数：M × N；Submodule.prod C₁ C₂；PointedCone.map (LinearMap.snd R M N) F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.IsFaceOf.map`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3}
 [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [ins
t_3 : AddCommG…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `LinearEquiv.prodComm_apply`：∀ (R : Type u_3) (M : Type u_4) (N : Type u_
5) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [
inst_3 : _root_.…
· 使用定理 `AddSubsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Add M] (carrier 
carrier_1 : Set M) (e_carrier : carrier = carrier_1)   (add_mem' : ∀ {a b : M}, 
a ∈ carrier → b ∈ c…
· 使用定理 `AddSubmonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : AddZeroClass M] (to
AddSubsemigroup toAddSubsemigroup_1 : AddSubsemigroup M)   (e_toAddSubsemigroup 
: toAddSubsemigr…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PointedCone.ext`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [in
st_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [
inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `PointedCone.IsFaceOf.fst`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3}
 [inst : DivisionRing R] [inst_1 : LinearOrder R]   [inst_2 : IsOrderedRing R] [
inst_3 : AddCo…
· 使用定理 `Set.image_swap_prod`：image_swap_prod (s : Set α) (t : Set β) : Prod.swap
 '' s ×ˢ t = t ×ˢ s
· 使用定理 `Submodule.mk.congr_simp`：∀ {R : Type u} {M : Type v} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (toAddSubmonoid toAdd
Submonoid_1 :…

--- 原说明 ---
The projection of a face of a product cone onto the second component is a face o
f the
projection of the product cone onto the second component.
-/
protected theorem snd {C₁ : PointedCone R M} {C₂ : PointedCone R N} {F : PointedCone R (M × N)}
    (hF : F.IsFaceOf (C₁.prod C₂)) : (F.map (.snd R M N)).IsFaceOf C₂ := by
  have := hF.map _ (LinearEquiv.prodComm R M N).injective
  convert IsFaceOf.fst (by simpa [PointedCone.map, Submodule.map])
  ext; simp

end Prod

end IsFaceOf

end DivisionRing

end PointedCone

