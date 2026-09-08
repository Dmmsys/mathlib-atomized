/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Bases and scalar multiplication

This file defines the scalar multiplication of bases by multiplying each basis vector.

-/

@[expose] public section

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι R R₂ M : Type*}

namespace Module.Basis
variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

section SMul
variable {G G'}
variable [Group G] [Group G']
variable [DistribMulAction G M] [DistribMulAction G' M]
variable [SMulCommClass G R M] [SMulCommClass G' R M]

/-- The action on a `Basis` by acting on each element.

See also `Basis.unitsSMul` and `Basis.groupSMul`, for the cases when a different action is applied
to each basis element. -/
/-
**Module.Basis.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on a `Basis` by acting on each element.

See also `Basis.unitsSMul` and `Basis.groupSMul`, for the cases when a different
 action is applied
to each basis element.
-/
instance : SMul G (Basis ι R M) where
  smul g b := b.map <| DistribMulAction.toLinearEquiv _ _ g

@[simp]
/-
**Module.Basis.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：smul_apply (g : G) (b : Basis ι R M) (i : ι) : (g • b) i = g • b i
参数：g : G；b : Basis ι R M；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (g : G) (b : Basis ι R M) (i : ι) : (g • b) i = g • b i := rfl
/-
**Module.Basis.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {G : Type u_5} [inst_3 : Grou
p G] [inst_4 : DistribMulAction G M]   [inst_5 : SMulCommClass G R M] (g : G) (b
 : Module.Basis ι R M), ⇑(g • b) = g • ⇑b
参数：g : G；b : Module.Basis ι R M；g • b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] theorem coe_smul (g : G) (b : Basis ι R M) : ⇑(g • b) = g • ⇑b := rfl

/-- When the group in question is the automorphisms, `•` coincides with `Basis.map`. -/
@[simp]
/-
**Module.Basis.smul_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：smul_eq_map (g : M ≃ₗ[R] M) (b : Basis ι R M) : g • b = b.map g
参数：g : M ≃ₗ[R] M；b : Basis ι R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the group in question is the automorphisms, `•` coincides with `Basis.map`.
-/
theorem smul_eq_map (g : M ≃ₗ[R] M) (b : Basis ι R M) : g • b = b.map g := rfl
/-
**Module.Basis.repr_smul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {G : Type u_5} [inst_3 : Grou
p G] [inst_4 : DistribMulAction G M]   [inst_5 : SMulCommClass G R M] (g : G) (b
 : Module.Basis ι R M),   (g • b).repr = (DistribMulAction.toLinearEquiv R M g).
symm ≪≫ₗ b.repr
参数：g : G；b : Module.Basis ι R M；g • b；DistribMulAction.toLinearEquiv R M g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem repr_smul (g : G) (b : Basis ι R M) :
    (g • b).repr = (DistribMulAction.toLinearEquiv _ _ g).symm.trans b.repr := rfl
/-
**Module.Basis.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction G (Basis ι R M) :=
  Function.Injective.mulAction _ DFunLike.coe_injective coe_smul
/-
**Module.Basis.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass G G' M] : SMulCommClass G G' (Basis ι R M) where
  smul_comm _g _g' _b := DFunLike.ext _ _ fun _ => smul_comm _ _ _
/-
**Module.Basis.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul G G'] [IsScalarTower G G' M] : IsScalarTower G G' (Basis ι R M) where
  smul_assoc _g _g' _b := DFunLike.ext _ _ fun _ => smul_assoc _ _ _

end SMul

section CommSemiring

variable {v : ι → M} {x y : M}

/-
**Module.Basis.groupSMul_span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：groupSMul_span_eq_top {G : Type*} [Group G] [SMul G R] [MulAction G M] [Is
ScalarTower G R M] {v : ι -> M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι
 -> G} : Submodule.span R (Set.range (w • v)) = ⊤
参数：hv : Submodule.span R (Set.range v) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Submodule.mem_span`：mem_span : x in span R s ↔ forall p : Submodule R M,
 s subseteq p -> x in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
-/
theorem groupSMul_span_eq_top {G : Type*} [Group G] [SMul G R] [MulAction G M]
    [IsScalarTower G R M] {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι → G} :
    Submodule.span R (Set.range (w • v)) = ⊤ := by
  rw [eq_top_iff]
  intro j hj
  rw [← hv] at hj
  rw [Submodule.mem_span] at hj ⊢
  refine fun p hp => hj p fun u hu => ?_
  obtain ⟨i, rfl⟩ := hu
  have : ((w i)⁻¹ • (1 : R)) • w i • v i ∈ p := p.smul_mem ((w i)⁻¹ • (1 : R)) (hp ⟨i, rfl⟩)
  rwa [smul_one_smul, inv_smul_smul] at this

/-- Given a basis `v` and a map `w` such that for all `i`, `w i` are elements of a group,
`groupSMul` provides the basis corresponding to `w • v`. -/
/-
**Module.Basis.groupSMul** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：groupSMul {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G
 M] [IsScalarTower G R M] [SMulCommClass G R M] (v : Basis ι R M) (w : ι -> G) :
 Basis ι R M
参数：v : Basis ι R M；w : ι -> G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a basis `v` and a map `w` such that for all `i`, `w i` are elements of a g
roup,
`groupSMul` provides the basis corresponding to `w • v`.
-/
def groupSMul {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] (v : Basis ι R M) (w : ι → G) : Basis ι R M :=
  Basis.mk (LinearIndependent.group_smul v.linearIndependent w) (groupSMul_span_eq_top v.span_eq).ge
/-
**Module.Basis.groupSMul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：groupSMul_apply {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAc
tion G M] [IsScalarTower G R M] [SMulCommClass G R M] {v : Basis ι R M} {w : ι -
> G} (i : ι) : v.groupSMul w i = (w • (v : ι -> M)) i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.mk_apply`：mk_apply (i : ι) : Basis.mk hli hsp i = v i
· 使用定理 `LinearIndependent.group_smul`：LinearIndependent.group_smul {G : Type*} [
hG : Group G] [MulAction G R] [SMul G M] [IsScalarTower G R M] [SMulCommClass G 
R M] {v : ι -> M} …
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Module.Basis.groupSMul_span_eq_top`：groupSMul_span_eq_top {G : Type*} [G
roup G] [SMul G R] [MulAction G M] [IsScalarTower G R M] {v : ι -> M} (hv : Subm
odule.span R (Set.range …
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
-/
theorem groupSMul_apply {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] {v : Basis ι R M} {w : ι → G} (i : ι) :
    v.groupSMul w i = (w • (v : ι → M)) i :=
  mk_apply (LinearIndependent.group_smul v.linearIndependent w)
    (groupSMul_span_eq_top v.span_eq).ge i
/-
**Module.Basis.units_smul_span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：units_smul_span_eq_top {v : ι -> M} (hv : Submodule.span R (Set.range v) =
 ⊤) {w : ι -> Rˣ} : Submodule.span R (Set.range (w • v)) = ⊤
参数：hv : Submodule.span R (Set.range v) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.groupSMul_span_eq_top`：groupSMul_span_eq_top {G : Type*} [G
roup G] [SMul G R] [MulAction G M] [IsScalarTower G R M] {v : ι -> M} (hv : Subm
odule.span R (Set.range …
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
-/
theorem units_smul_span_eq_top {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι → Rˣ} :
    Submodule.span R (Set.range (w • v)) = ⊤ :=
  groupSMul_span_eq_top hv

/-- Given a basis `v` and a map `w` such that for all `i`, `w i` is a unit, `unitsSMul`
provides the basis corresponding to `w • v`. -/
/-
**Module.Basis.unitsSMul** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：unitsSMul (v : Basis ι R M) (w : ι -> Rˣ) : Basis ι R M
参数：v : Basis ι R M；w : ι -> Rˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a basis `v` and a map `w` such that for all `i`, `w i` is a unit, `unitsSM
ul`
provides the basis corresponding to `w • v`.
-/
def unitsSMul (v : Basis ι R M) (w : ι → Rˣ) : Basis ι R M :=
  Basis.mk (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge
/-
**Module.Basis.unitsSMul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：unitsSMul_apply {v : Basis ι R M} {w : ι -> Rˣ} (i : ι) : unitsSMul v w i 
= w i • v i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.mk_apply`：mk_apply (i : ι) : Basis.mk hli hsp i = v i
· 使用定理 `LinearIndependent.units_smul`：LinearIndependent.units_smul {v : ι -> M} 
(hv : LinearIndependent R v) (w : ι -> Rˣ) : LinearIndependent R (w • v)
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Module.Basis.units_smul_span_eq_top`：units_smul_span_eq_top {v : ι -> M}
 (hv : Submodule.span R (Set.range v) = ⊤) {w : ι -> Rˣ} : Submodule.span R (Set
.range (w • v)) = ⊤
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
-/
theorem unitsSMul_apply {v : Basis ι R M} {w : ι → Rˣ} (i : ι) : unitsSMul v w i = w i • v i :=
  mk_apply (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge i

variable [CommSemiring R₂] [Module R₂ M]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Module.Basis.coord_unitsSMul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coord_unitsSMul (e : Basis ι R₂ M) (w : ι -> R₂ˣ) (i : ι) : (unitsSMul e w
).coord i = (w i)⁻¹ • e.coord i
参数：e : Basis ι R₂ M；w : ι -> R₂ˣ；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem coord_unitsSMul (e : Basis ι R₂ M) (w : ι → R₂ˣ) (i : ι) :
    (unitsSMul e w).coord i = (w i)⁻¹ • e.coord i := by
  classical
    apply e.ext
    intro j
    trans ((unitsSMul e w).coord i) ((w j)⁻¹ • (unitsSMul e w) j)
    · simp [Basis.unitsSMul, ← mul_smul]
    simp only [Basis.coord_apply, LinearMap.smul_apply, Basis.repr_self, Units.smul_def,
      map_smul, Finsupp.single_apply]
    split_ifs with h <;> simp [h]

@[simp]
/-
**Module.Basis.repr_unitsSMul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_unitsSMul (e : Basis ι R₂ M) (w : ι -> R₂ˣ) (v : M) (i : ι) : (e.unit
sSMul w).repr v i = (w i)⁻¹ • e.repr v i
参数：e : Basis ι R₂ M；w : ι -> R₂ˣ；v : M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Basis.coord_unitsSMul`：coord_unitsSMul (e : Basis ι R₂ M) (w : ι 
-> R₂ˣ) (i : ι) : (unitsSMul e w).coord i = (w i)⁻¹ • e.coord i
-/
theorem repr_unitsSMul (e : Basis ι R₂ M) (w : ι → R₂ˣ) (v : M) (i : ι) :
    (e.unitsSMul w).repr v i = (w i)⁻¹ • e.repr v i :=
  congr_arg (fun f : M →ₗ[R₂] R₂ => f v) (e.coord_unitsSMul w i)

/-- A version of `unitsSMul` that uses `IsUnit`. -/
/-
**Module.Basis.isUnitSMul** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：isUnitSMul (v : Basis ι R M) {w : ι -> R} (hw : forall i, IsUnit (w i)) : 
Basis ι R M
参数：v : Basis ι R M；hw : forall i, IsUnit (w i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `unitsSMul` that uses `IsUnit`.
-/
def isUnitSMul (v : Basis ι R M) {w : ι → R} (hw : ∀ i, IsUnit (w i)) : Basis ι R M :=
  unitsSMul v fun i => (hw i).unit
/-
**Module.Basis.isUnitSMul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：isUnitSMul_apply {v : Basis ι R M} {w : ι -> R} (hw : forall i, IsUnit (w 
i)) (i : ι) : v.isUnitSMul hw i = w i • v i
参数：hw : forall i, IsUnit (w i)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.unitsSMul_apply`：unitsSMul_apply {v : Basis ι R M} {w : ι -
> Rˣ} (i : ι) : unitsSMul v w i = w i • v i
-/
theorem isUnitSMul_apply {v : Basis ι R M} {w : ι → R} (hw : ∀ i, IsUnit (w i)) (i : ι) :
    v.isUnitSMul hw i = w i • v i :=
  unitsSMul_apply i
/-
**Module.Basis.repr_isUnitSMul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：repr_isUnitSMul {v : Basis ι R₂ M} {w : ι -> R₂} (hw : forall i, IsUnit (w
 i)) (x : M) (i : ι) : (v.isUnitSMul hw).repr x i = (hw i).unit⁻¹ • v.repr x i
参数：hw : forall i, IsUnit (w i)；x : M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.repr_unitsSMul`：repr_unitsSMul (e : Basis ι R₂ M) (w : ι ->
 R₂ˣ) (v : M) (i : ι) : (e.unitsSMul w).repr v i = (w i)⁻¹ • e.repr v i
-/
theorem repr_isUnitSMul {v : Basis ι R₂ M} {w : ι → R₂} (hw : ∀ i, IsUnit (w i)) (x : M) (i : ι) :
    (v.isUnitSMul hw).repr x i = (hw i).unit⁻¹ • v.repr x i :=
  repr_unitsSMul _ _ _ _

end CommSemiring
end Module.Basis

