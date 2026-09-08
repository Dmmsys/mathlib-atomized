/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# The algebraic dual of a cone

Given a bilinear pairing `p` between two `R`-modules `M` and `N` and a set `s` in `M`, we define
`PointedCone.dual p s` to be the pointed cone in `N` consisting of all points `y` such that
`0 ≤ p x y` for all `x ∈ s`.

When the pairing is perfect, this gives us the algebraic dual of a cone. This is developed here.
When the pairing is continuous and perfect (as a continuous pairing), this gives us the topological
dual instead. See `Mathlib/Analysis/Convex/Cone/Dual.lean` for that case.

## Implementation notes

We do not provide a `ConvexCone`-valued version of `PointedCone.dual` since the dual cone of any set
always contains `0`, i.e. is a pointed cone.
Furthermore, the strict version `{y | ∀ x ∈ s, 0 < p x y}` is a candidate to the name
`ConvexCone.dual`.

-/

@[expose] public section

assert_not_exists TopologicalSpace Real Cardinal

open Function LinearMap Pointwise Set

namespace PointedCone

section CommSemiring

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} {s t : Set M} {y : N}

local notation3 "R≥0" => {c : R // 0 ≤ c}

variable (p) in
/-- The dual cone of a set `s` with respect to a bilinear pairing `p` is the cone consisting of all
points `y` such that for all points `x ∈ s` we have `0 ≤ p x y`. -/
/-
**PointedCone.dual** 是 Mathlib 中的一个定义，位于命名空间 `PointedCone`。
形式化陈述：dual (s : Set M) : PointedCone R N where carrier
参数：s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dual cone of a set `s` with respect to a bilinear pairing `p` is the cone co
nsisting of all
points `y` such that for all points `x ∈ s` we have `0 ≤ p x y`.
-/
def dual (s : Set M) : PointedCone R N where
  carrier := {y | ∀ ⦃x⦄, x ∈ s → 0 ≤ p x y}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [map_add]; exact add_nonneg (hu hx) (hv hx)
  smul_mem' c y hy x hx := by rw [← Nonneg.coe_smul, map_smul]; exact mul_nonneg c.2 (hy hx)
/-
**PointedCone.mem_dual** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialOrder R] [inst_2
 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoid M] [inst_4 : _root_
.Module R M] {N : Type u_3} [inst_5 : AddCommMonoid N]   [inst_6 : _root_.Module
 R N] {p : M →ₗ[R] N →ₗ[R] R} {s : Set M} {y : N},   y ∈ PointedCone.dual p s ↔ 
∀ ⦃x : M⦄, x ∈ s → 0 ≤ (p x) y
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
@[simp] lemma mem_dual : y ∈ dual p s ↔ ∀ ⦃x⦄, x ∈ s → 0 ≤ p x y := .rfl
/-
**PointedCone.dual_empty** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialOrder R] [inst_2
 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoid M] [inst_4 : _root_
.Module R M] {N : Type u_3} [inst_5 : AddCommMonoid N]   [inst_6 : _root_.Module
 R N] {p : M →ₗ[R] N →ₗ[R] R}, PointedCone.dual p ∅ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.ext`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [in
st_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [
inst_…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma dual_empty : dual p ∅ = ⊤ := by ext; simp
/-
**PointedCone.dual_zero** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialOrder R] [inst_2
 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoid M] [inst_4 : _root_
.Module R M] {N : Type u_3} [inst_5 : AddCommMonoid N]   [inst_6 : _root_.Module
 R N] {p : M →ₗ[R] N →ₗ[R] R}, PointedCone.dual p 0 = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.ext`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [in
st_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [
inst_…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma dual_zero : dual p 0 = ⊤ := by ext; simp
/-
**PointedCone.dual_singleton_zero** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialOrder R] [inst_2
 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoid M] [inst_4 : _root_
.Module R M] {N : Type u_3} [inst_5 : AddCommMonoid N]   [inst_6 : _root_.Module
 R N] {p : M →ₗ[R] N →ₗ[R] R}, PointedCone.dual p {0} = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.dual_zero`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 
: PartialOrder R] [inst_2 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommM
onoid M] [i…
-/
@[simp] lemma dual_singleton_zero : dual p {0} = ⊤ := dual_zero
/-
**PointedCone.dual_ker** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialOrder R] [inst_2
 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoid M] [inst_4 : _root_
.Module R M] {N : Type u_3} [inst_5 : AddCommMonoid N]   [inst_6 : _root_.Module
 R N] {p : M →ₗ[R] N →ₗ[R] R}, PointedCone.dual p ↑p.ker = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.ext`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [in
st_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [
inst_…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma dual_ker : dual p (ker p) = ⊤ := by ext; simp +contextual
/-
**PointedCone.dual_anti** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialOrder R] [inst_2
 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoid M] [inst_4 : _root_
.Module R M] {N : Type u_3} [inst_5 : AddCommMonoid N]   [inst_6 : _root_.Module
 R N] {p : M →ₗ[R] N →ₗ[R] R} {s t : Set M},   t ⊆ s → PointedCone.dual p s ≤ Po
intedCone.dual p t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
@[gcongr] lemma dual_anti (h : t ⊆ s) : dual p s ≤ dual p t := fun _y hy _x hx ↦ hy (h hx)

alias dual_le_dual := dual_anti
/-
**PointedCone.dual_antitone** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：dual_antitone : Antitone (dual p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.dual_anti`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 
: PartialOrder R] [inst_2 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommM
onoid M] [i…
-/
lemma dual_antitone : Antitone (dual p) := fun _ _ h => dual_anti h

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `p x`. -/
/-
**PointedCone.dual_singleton** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：dual_singleton (x : M) : dual p {x} = (positive R R).comap (p x)
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.ext`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [in
st_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [
inst_…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsOrderedRing.toIsOrderedModule`：∀ {α : Type u_1} [inst : Semiring α] [i
nst_1 : PartialOrder α] [IsOrderedRing α], IsOrderedModule α α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The inner dual cone of a singleton is given by the preimage of the positive cone
 under the
linear map `p x`.
-/
lemma dual_singleton (x : M) : dual p {x} = (positive R R).comap (p x) := by ext; simp
/-
**PointedCone.dual_union** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：dual_union (s t : Set M) : dual p (s union t) = dual p s ⊓ dual p t
参数：s t : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.ext`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [in
st_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [
inst_…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma dual_union (s t : Set M) : dual p (s ∪ t) = dual p s ⊓ dual p t := by aesop
/-
**PointedCone.dual_insert** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：dual_insert (x : M) (s : Set M) : dual p (insert x s) = dual p {x} ⊓ dual 
p s
参数：x : M；s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用引理 `PointedCone.dual_union`：dual_union (s t : Set M) : dual p (s union t) = 
dual p s ⊓ dual p t
-/
lemma dual_insert (x : M) (s : Set M) : dual p (insert x s) = dual p {x} ⊓ dual p s := by
  rw [insert_eq, dual_union]
/-
**PointedCone.dual_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：dual_iUnion {ι : Sort*} (f : ι -> Set M) : dual p (⋃ i, f i) = ⨅ i, dual p
 (f i)
参数：f : ι -> Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.ext`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [in
st_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [
inst_…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dual_iUnion {ι : Sort*} (f : ι → Set M) : dual p (⋃ i, f i) = ⨅ i, dual p (f i) := by
  ext; simp [forall_comm (α := M)]
/-
**PointedCone.dual_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：dual_sUnion (S : Set (Set M)) : dual p (⋃₀ S) = sInf (dual p '' S)
参数：S : Set (Set M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.ext`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [in
st_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [
inst_…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dual_sUnion (S : Set (Set M)) : dual p (⋃₀ S) = sInf (dual p '' S) := by
  ext; simp [forall_comm (α := M)]

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
/-
**PointedCone.dual_eq_iInter_dual_singleton** 是 Mathlib 中的一个引理，位于命名空间 `PointedCo
ne`。
形式化陈述：dual_eq_iInter_dual_singleton (s : Set M) : dual p s = ⋂ i : s, (dual p {i
.val} : Set N)
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The dual cone of `s` equals the intersection of dual cones of the points in `s`.
-/
lemma dual_eq_iInter_dual_singleton (s : Set M) :
    dual p s = ⋂ i : s, (dual p {i.val} : Set N) := by ext; simp

/-- Any set is a subset of its double dual cone. -/
/-
**PointedCone.subset_dual_dual** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：subset_dual_dual : s subseteq dual p.flip (dual p s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
Any set is a subset of its double dual cone.
-/
lemma subset_dual_dual : s ⊆ dual p.flip (dual p s) := fun _x hx _y hy ↦ hy hx
/-
**PointedCone.subset_dual_flip_iff_subset_dual** 是 Mathlib 中的一个定理，位于命名空间 `Pointe
dCone`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialOrder R] [inst_2
 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoid M] [inst_4 : _root_
.Module R M] {N : Type u_3} [inst_5 : AddCommMonoid N]   [inst_6 : _root_.Module
 R N] {p : M →ₗ[R] N →ₗ[R] R} {s : Set M} {t : Set N},   s ⊆ ↑(PointedCone.dual 
p.flip t) ↔ t ⊆ ↑(PointedCone.dual p s)
参数：PointedCone.dual p.flip t；PointedCone.dual p s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `PointedCone.subset_dual_dual`：subset_dual_dual : s subseteq dual p.flip 
(dual p s)
· 使用引理 `PointedCone.dual_antitone`：dual_antitone : Antitone (dual p)
-/
@[simp] lemma subset_dual_flip_iff_subset_dual {s : Set M} {t : Set N} :
    s ⊆ dual p.flip t ↔ t ⊆ dual p s := by
  constructor <;> exact (le_trans subset_dual_dual <| dual_antitone ·)

variable (s) in
/-
**PointedCone.dual_dual_flip_dual** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialOrder R] [inst_2
 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoid M] [inst_4 : _root_
.Module R M] {N : Type u_3} [inst_5 : AddCommMonoid N]   [inst_6 : _root_.Module
 R N] {p : M →ₗ[R] N →ₗ[R] R} (s : Set M),   PointedCone.dual p ↑(PointedCone.du
al p.flip ↑(PointedCone.dual p s)) = PointedCone.dual p s
参数：s : Set M；PointedCone.dual p.flip ↑(PointedCone.dual p s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.dual_anti`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 
: PartialOrder R] [inst_2 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommM
onoid M] [i…
· 使用引理 `PointedCone.subset_dual_dual`：subset_dual_dual : s subseteq dual p.flip 
(dual p s)
-/
@[simp] lemma dual_dual_flip_dual : dual p (dual p.flip (dual p s)) = dual p s :=
  le_antisymm (dual_anti subset_dual_dual) subset_dual_dual
/-
**PointedCone.dual_flip_dual_dual_flip** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialOrder R] [inst_2
 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoid M] [inst_4 : _root_
.Module R M] {N : Type u_3} [inst_5 : AddCommMonoid N]   [inst_6 : _root_.Module
 R N] {p : M →ₗ[R] N →ₗ[R] R} (s : Set N),   PointedCone.dual p.flip ↑(PointedCo
ne.dual p ↑(PointedCone.dual p.flip s)) = PointedCone.dual p.flip s
参数：s : Set N；PointedCone.dual p ↑(PointedCone.dual p.flip s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.dual_dual_flip_dual`：∀ {R : Type u_1} [inst : CommSemiring R
] [inst_1 : PartialOrder R] [inst_2 : IsOrderedRing R] {M : Type u_2}   [inst_3 
: AddCommMonoid M] [i…
-/
@[simp] lemma dual_flip_dual_dual_flip (s : Set N) :
    dual p.flip (dual p (dual p.flip s)) = dual p.flip s := dual_dual_flip_dual _

@[simp]
/-
**PointedCone.dual_hull** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：dual_hull (s : Set M) : dual p (hull R s) = dual p s
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.dual_anti`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 
: PartialOrder R] [inst_2 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommM
onoid M] [i…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `LinearMap.add_apply`：add_apply (f g : M ->ₛₗ[σ₁₂] M₂) (x : M) : (f + g) 
x = f x + g x
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `Nonneg.mk_smul`：mk_smul (a) (ha) (x : S) : (⟨a, ha⟩ : R>=0) • x = a • x
· 使用定理 `LinearMap.smul_apply`：smul_apply (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M) : 
(a • f) x = a • f x
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
-/
lemma dual_hull (s : Set M) : dual p (hull R s) = dual p s := by
  refine le_antisymm (dual_anti Submodule.subset_span) (fun x hx y hy => ?_)
  induction hy using Submodule.span_induction with
  | mem _y h => exact hx h
  | zero => simp
  | add y z _hy _hz hy hz => rw [map_add, add_apply]; exact add_nonneg hy hz
  | smul t y _hy hy => rw [map_smul_of_tower, Nonneg.mk_smul, smul_apply]; exact mul_nonneg t.2 hy

@[deprecated "`PointedCone.span` was renamed to `PointedCone.hull`" (since := "2026-03-22")]
alias dual_span := dual_hull
/-
**PointedCone.dual_sup** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialOrder R] [inst_2
 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoid M] [inst_4 : _root_
.Module R M] {N : Type u_3} [inst_5 : AddCommMonoid N]   [inst_6 : _root_.Module
 R N] {p : M →ₗ[R] N →ₗ[R] R} (C D : PointedCone R M),   PointedCone.dual p ↑(C 
⊔ D) = PointedCone.dual p (↑C ∪ ↑D)
参数：C D : PointedCone R M；C ⊔ D；↑C ∪ ↑D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Submodule.span_coe_eq_restrictScalars`：span_coe_eq_restrictScalars [Semi
ring S] [SMul S R] [Module S M] [IsScalarTower S R M] : span S (p : Set M) = p.r
estrictScalars S
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `Submodule.span_union`：span_union (s t : Set M) : span R (s union t) = sp
an R s ⊔ span R t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma dual_sup (C D : PointedCone R M) : dual p (C ⊔ D : PointedCone R M) = dual p (C ∪ D)
  := by simp [← dual_hull]

variable {M' : Type*} [AddCommMonoid M'] [Module R M']
/-
**PointedCone.dual_image** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialOrder R] [inst_2
 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoid M] [inst_4 : _root_
.Module R M] {N : Type u_3} [inst_5 : AddCommMonoid N]   [inst_6 : _root_.Module
 R N] {p : M →ₗ[R] N →ₗ[R] R} {M' : Type u_4} [inst_7 : AddCommMonoid M']   [ins
t_8 : _root_.Module R M'] (s : Set M') (q : M' →ₗ[R] M),   PointedCone.dual p (⇑
q '' s) = PointedCone.dual (p ∘ₗ q) s
参数：s : Set M'；q : M' →ₗ[R] M；⇑q '' s；p ∘ₗ q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.ext`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [in
st_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [
inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma dual_image (s : Set M') (q : M' →ₗ[R] M) : dual p (q '' s) = dual (p.comp q) s := by
  ext; simp

/-- Duality with respect to a general bilinear map can be expressed as duality using the
  identity pairing. -/
/-
**PointedCone.dual_eq_dual_id_image** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：dual_eq_dual_id_image (s : Set M) : dual p s = dual .id (p '' s)
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PointedCone.dual_image`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddComm
Monoid M] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Duality with respect to a general bilinear map can be expressed as duality using
 the
  identity pairing.
-/
lemma dual_eq_dual_id_image (s : Set M) : dual p s = dual .id (p '' s) := by simp

/-- Duality with respect to a general bilinear map can be expressed as duality using the
  identity pairing. -/
/-
**PointedCone.dual_eq_dual_id_map** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：dual_eq_dual_id_map (C : PointedCone R M) : dual p C = dual .id (map p C)
参数：C : PointedCone R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PointedCone.dual_image`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1
 : PartialOrder R] [inst_2 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddComm
Monoid M] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Duality with respect to a general bilinear map can be expressed as duality using
 the
  identity pairing.
-/
lemma dual_eq_dual_id_map (C : PointedCone R M) : dual p C = dual .id (map p C) := by simp

/-- Duality with respect to a general bilinear map can be expressed as duality using the
  standard pairing `Dual.eval`. -/
/-
**PointedCone.dual_eq_comap_dual_eval** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：dual_eq_comap_dual_eval (s : Set M) : dual p s = comap p.flip (dual (Modul
e.Dual.eval R M) s)
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.ext`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [in
st_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [
inst_…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Duality with respect to a general bilinear map can be expressed as duality using
 the
  standard pairing `Dual.eval`.
-/
lemma dual_eq_comap_dual_eval (s : Set M) :
    dual p s = comap p.flip (dual (Module.Dual.eval R M) s) := by
  ext; simp

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

/-
**PointedCone.dual_univ** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：dual_univ (hp : Injective p.flip) : dual p univ = 0
参数：hp : Injective p.flip。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma dual_univ (hp : Injective p.flip) : dual p univ = 0 := by
  refine le_antisymm (fun y hy ↦ (map_eq_zero_iff p.flip hp).1 ?_) (by simp)
  ext x
  exact (hy <| mem_univ x).antisymm' <| by simpa using hy <| mem_univ (-x)

variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
/-
**PointedCone.dual_neg** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : PartialOrder R] [inst_2 : I
sOrderedRing R] {M : Type u_2}   [inst_3 : AddCommGroup M] [inst_4 : _root_.Modu
le R M] {N : Type u_4} [inst_5 : AddCommGroup N]   [inst_6 : _root_.Module R N] 
{p : M →ₗ[R] N →ₗ[R] R} {s : Set M}, PointedCone.dual p (-s) = -PointedCone.dual
 p s
参数：-s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedCone.ext`：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [in
st_1 : PartialOrder R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid E] [
inst_…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma dual_neg {s : Set M} : dual p (-s) = -dual p s := by ext; simp

end CommRing

end PointedCone

