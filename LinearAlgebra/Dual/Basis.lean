/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle, Kyle Miller
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Bases of dual vector spaces

The dual space of an $R$-module $M$ is the $R$-module of $R$-linear maps $M \to R$.
This file concerns bases on dual vector spaces.

## Main definitions

* Bases:
  * `Basis.toDual` produces the map `M →ₗ[R] Dual R M` associated to a basis for an `R`-module `M`.
  * `Basis.toDualEquiv` is the equivalence `M ≃ₗ[R] Dual R M` associated to a finite basis.
  * `Basis.dualBasis` is a basis for `Dual R M` given a finite basis for `M`.
  * `Module.DualBases e ε` is the proposition that the families `e` of vectors and `ε` of dual
    vectors have the characteristic properties of a basis and a dual.

## Main results

* Bases:
  * `Module.DualBases.basis` and `Module.DualBases.coe_basis`: if `e` and `ε` form a dual pair,
    then `e` is a basis.
  * `Module.DualBases.coe_dualBasis`: if `e` and `ε` form a dual pair,
    then `ε` is a basis.
-/

@[expose] public section

open Module Dual Submodule LinearMap Function

noncomputable section

namespace Module.Basis

universe u v w uR uM uK uV uι
variable {R : Type uR} {M : Type uM} {K : Type uK} {V : Type uV} {ι : Type uι}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [DecidableEq ι]
variable (b : Basis ι R M)

/-- The linear map from a vector space equipped with basis to its dual vector space,
taking basis elements to corresponding dual basis elements. -/
/-
**Module.Basis.toDual** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：toDual : M ->ₗ[R] Module.Dual R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map from a vector space equipped with basis to its dual vector space,
taking basis elements to corresponding dual basis elements.
-/
def toDual : M →ₗ[R] Module.Dual R M :=
  b.constr ℕ fun v => b.constr ℕ fun w => if w = v then (1 : R) else 0
/-
**Module.Basis.toDual_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toDual_apply (i j : ι) : b.toDual (b i) (b j) = if i = j then 1 else 0
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.toDual.eq_1`：∀ {R : Type uR} {M : Type uM} {ι : Type uι} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : Deci…
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toDual_apply (i j : ι) : b.toDual (b i) (b j) = if i = j then 1 else 0 := by
  rw [toDual, constr_basis b, constr_basis b]
  simp only [eq_comm]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Module.Basis.toDual_linearCombination_left** 是 Mathlib 中的一个定理，位于命名空间 `Module.B
asis`。
形式化陈述：toDual_linearCombination_left (f : ι ->₀ R) (i : ι) : b.toDual (Finsupp.li
nearCombination R b f) (b i) = f i
参数：f : ι ->₀ R；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.sum_apply`：sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) 
(b : M) : (∑ d in t, f d) b = ∑ d in t, f d b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Module.Basis.toDual_apply`：toDual_apply (i j : ι) : b.toDual (b i) (b j)
 = if i = j then 1 else 0
· 使用定理 `mul_boole`：mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (a * if P then 1 else 0) = if P then a else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.if_mem_support`：if_mem_support [DecidableEq α] {N : Type*} [Zero
 N] (f : α ->₀ N) (a : α) : (if a in f.support then f a else 0) = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toDual_linearCombination_left (f : ι →₀ R) (i : ι) :
    b.toDual (Finsupp.linearCombination R b f) (b i) = f i := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, LinearMap.sum_apply]
  simp_rw [map_smul, LinearMap.smul_apply, toDual_apply, smul_eq_mul, mul_boole,
    Finset.sum_ite_eq', Finsupp.if_mem_support]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Module.Basis.toDual_linearCombination_right** 是 Mathlib 中的一个定理，位于命名空间 `Module.
Basis`。
形式化陈述：toDual_linearCombination_right (f : ι ->₀ R) (i : ι) : b.toDual (b i) (Fin
supp.linearCombination R b f) = f i
参数：f : ι ->₀ R；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Module.Basis.toDual_apply`：toDual_apply (i j : ι) : b.toDual (b i) (b j)
 = if i = j then 1 else 0
· 使用定理 `mul_boole`：mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (a * if P then 1 else 0) = if P then a else 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.if_mem_support`：if_mem_support [DecidableEq α] {N : Type*} [Zero
 N] (f : α ->₀ N) (a : α) : (if a in f.support then f a else 0) = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toDual_linearCombination_right (f : ι →₀ R) (i : ι) :
    b.toDual (b i) (Finsupp.linearCombination R b f) = f i := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  simp_rw [map_smul, toDual_apply, smul_eq_mul, mul_boole, Finset.sum_ite_eq,
    Finsupp.if_mem_support]
/-
**Module.Basis.toDual_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toDual_apply_left (m : M) (i : ι) : b.toDual m (b i) = b.repr m i
参数：m : M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.toDual_linearCombination_left`：toDual_linearCombination_lef
t (f : ι ->₀ R) (i : ι) : b.toDual (Finsupp.linearCombination R b f) (b i) = f i
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
-/
theorem toDual_apply_left (m : M) (i : ι) : b.toDual m (b i) = b.repr m i := by
  rw [← b.toDual_linearCombination_left, b.linearCombination_repr]
/-
**Module.Basis.toDual_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toDual_apply_right (i : ι) (m : M) : b.toDual (b i) m = b.repr m i
参数：i : ι；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.toDual_linearCombination_right`：toDual_linearCombination_ri
ght (f : ι ->₀ R) (i : ι) : b.toDual (b i) (Finsupp.linearCombination R b f) = f
 i
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
-/
theorem toDual_apply_right (i : ι) (m : M) : b.toDual (b i) m = b.repr m i := by
  rw [← b.toDual_linearCombination_right, b.linearCombination_repr]
/-
**Module.Basis.coe_toDual_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_toDual_self (i : ι) : b.toDual (b i) = b.coord i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.Basis.toDual_apply_right`：toDual_apply_right (i : ι) (m : M) : b.
toDual (b i) m = b.repr m i
-/
theorem coe_toDual_self (i : ι) : b.toDual (b i) = b.coord i := by
  ext
  apply toDual_apply_right

/-- `h.toDualFlip v` is the linear map sending `w` to `h.toDual w v`. -/
/-
**Module.Basis.toDualFlip** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：toDualFlip (m : M) : M ->ₗ[R] R
参数：m : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`h.toDualFlip v` is the linear map sending `w` to `h.toDual w v`.
-/
def toDualFlip (m : M) : M →ₗ[R] R :=
  b.toDual.flip m
/-
**Module.Basis.toDualFlip_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toDualFlip_apply (m₁ m₂ : M) : b.toDualFlip m₁ m₂ = b.toDual m₂ m₁
参数：m₁ m₂ : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDualFlip_apply (m₁ m₂ : M) : b.toDualFlip m₁ m₂ = b.toDual m₂ m₁ :=
  rfl
/-
**Module.Basis.toDual_eq_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toDual_eq_repr (m : M) (i : ι) : b.toDual m (b i) = b.repr m i
参数：m : M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.toDual_apply_left`：toDual_apply_left (m : M) (i : ι) : b.to
Dual m (b i) = b.repr m i
-/
theorem toDual_eq_repr (m : M) (i : ι) : b.toDual m (b i) = b.repr m i :=
  b.toDual_apply_left m i
/-
**Module.Basis.toDual_eq_equivFun** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toDual_eq_equivFun [Finite ι] (m : M) (i : ι) : b.toDual m (b i) = b.equiv
Fun m i
参数：m : M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.equivFun_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u
_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] [inst_3 : Finit…
· 使用定理 `Module.Basis.toDual_eq_repr`：toDual_eq_repr (m : M) (i : ι) : b.toDual m
 (b i) = b.repr m i
-/
theorem toDual_eq_equivFun [Finite ι] (m : M) (i : ι) : b.toDual m (b i) = b.equivFun m i := by
  rw [b.equivFun_apply, toDual_eq_repr]
/-
**Module.Basis.toDual_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toDual_injective : Injective b.toDual
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Basis.ext_elem_iff`：ext_elem_iff {x y : M} : x = y ↔ forall i, b.
repr x i = b.repr y i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem toDual_injective : Injective b.toDual := fun x y h ↦ b.ext_elem_iff.mpr fun i ↦ by
  simp_rw [← toDual_eq_repr]; exact DFunLike.congr_fun h _
/-
**Module.Basis.toDual_inj** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toDual_inj (m : M) (a : b.toDual m = 0) : m = 0
参数：m : M；a : b.toDual m = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.Basis.toDual_injective`：toDual_injective : Injective b.toDual
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
-/
theorem toDual_inj (m : M) (a : b.toDual m = 0) : m = 0 :=
  b.toDual_injective (by rwa [map_zero])
/-
**Module.Basis.toDual_ker** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toDual_ker : LinearMap.ker b.toDual = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.ker_eq_bot'`：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ fo
rall m, f m = 0 -> m = 0
· 使用定理 `Module.Basis.toDual_inj`：toDual_inj (m : M) (a : b.toDual m = 0) : m = 0
-/
theorem toDual_ker : LinearMap.ker b.toDual = ⊥ :=
  ker_eq_bot'.mpr b.toDual_inj
/-
**Module.Basis.toDual_range** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toDual_range [Finite ι] : LinearMap.range b.toDual = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.toDual_linearCombination_left`：toDual_linearCombination_lef
t (f : ι ->₀ R) (i : ι) : b.toDual (Finsupp.linearCombination R b f) (b i) = f i
· 使用定理 `Finsupp.equivFunOnFinite_symm_apply_apply`：∀ {α : Type u_1} {M : Type u_
4} [inst : Zero M] [inst_1 : Finite α] (f : α → M) (a : α),   (Finsupp.equivFunO
nFinite.symm f) a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toDual_range [Finite ι] : LinearMap.range b.toDual = ⊤ :=
  eq_top_iff'.2 fun f => ⟨Finsupp.linearCombination R b <|
    Finsupp.equivFunOnFinite.symm fun i => f (b i), b.ext fun i => by simp⟩

omit [DecidableEq ι] in
@[simp]
/-
**Module.Basis.sum_dual_apply_smul_coord** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis
`。
形式化陈述：sum_dual_apply_smul_coord [Fintype ι] (f : Module.Dual R M) : (∑ x, f (b x
) • b.coord x) = f
参数：f : Module.Dual R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.sum_apply`：sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) 
(b : M) : (∑ d in t, f d) b = ∑ d in t, f d b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_dual_apply_smul_coord [Fintype ι] (f : Module.Dual R M) :
    (∑ x, f (b x) • b.coord x) = f := by
  ext m
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm (f _), ← smul_eq_mul,
    ← f.map_smul, ← map_sum, Basis.coord_apply, Basis.sum_repr]

section Finite

variable [Finite ι]

/-- A vector space is linearly equivalent to its dual space. -/
/-
**Module.Basis.toDualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：toDualEquiv : M ≃ₗ[R] Dual R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A vector space is linearly equivalent to its dual space.
-/
def toDualEquiv : M ≃ₗ[R] Dual R M :=
  .ofBijective b.toDual ⟨b.toDual_injective, range_eq_top.mp b.toDual_range⟩

-- `simps` times out when generating this
@[simp]
/-
**Module.Basis.toDualEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toDualEquiv_apply (m : M) : b.toDualEquiv m = b.toDual m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem toDualEquiv_apply (m : M) : b.toDualEquiv m = b.toDual m :=
  rfl

/-- Maps a basis for `V` to a basis for the dual space. -/
/-
**Module.Basis.dualBasis** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：dualBasis : Basis ι R (Dual R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps a basis for `V` to a basis for the dual space.
-/
def dualBasis : Basis ι R (Dual R M) :=
  b.map b.toDualEquiv

-- We use `j = i` to match `Basis.repr_self`
/-
**Module.Basis.dualBasis_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：dualBasis_apply_self (i j : ι) : b.dualBasis i (b j) = if j = i then 1 els
e 0
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Module.Basis.toDual_apply`：toDual_apply (i j : ι) : b.toDual (b i) (b j)
 = if i = j then 1 else 0
-/
theorem dualBasis_apply_self (i j : ι) : b.dualBasis i (b j) =
    if j = i then 1 else 0 := by
  convert! b.toDual_apply i j using 2
  rw [@eq_comm _ j i]
/-
**Module.Basis.linearCombination_dualBasis** 是 Mathlib 中的一个定理，位于命名空间 `Module.Bas
is`。
形式化陈述：linearCombination_dualBasis (f : ι ->₀ R) (i : ι) : Finsupp.linearCombinat
ion R b.dualBasis f (b i) = f i
参数：f : ι ->₀ R；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `LinearMap.sum_apply`：sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) 
(b : M) : (∑ d in t, f d) b = ∑ d in t, f d b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Module.Basis.dualBasis_apply_self`：dualBasis_apply_self (i j : ι) : b.du
alBasis i (b j) = if j = i then 1 else 0
· 使用定理 `mul_boole`：mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (a * if P then 1 else 0) = if P then a else 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearCombination_dualBasis (f : ι →₀ R) (i : ι) :
    Finsupp.linearCombination R b.dualBasis f (b i) = f i := by
  cases nonempty_fintype ι
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype, LinearMap.sum_apply]
  · simp_rw [LinearMap.smul_apply, smul_eq_mul, dualBasis_apply_self, mul_boole,
      Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  · intro
    rw [zero_smul]
/-
**Module.Basis.dualBasis_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {R : Type uR} {M : Type uM} {ι : Type uι} [inst : CommSemiring R] [inst_
1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : DecidableEq ι] (b 
: Module.Basis ι R M) [inst_4 : Finite ι]   (l : Module.Dual R M) (i : ι), (b.du
alBasis.repr l) i = l (b i)
参数：b : Module.Basis ι R M；l : Module.Dual R M；i : ι；b.dualBasis.repr l；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.linearCombination_dualBasis`：linearCombination_dualBasis (f
 : ι ->₀ R) (i : ι) : Finsupp.linearCombination R b.dualBasis f (b i) = f i
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
-/
@[simp] theorem dualBasis_repr (l : Dual R M) (i : ι) : b.dualBasis.repr l i = l (b i) := by
  rw [← linearCombination_dualBasis b, Basis.linearCombination_repr b.dualBasis l]
/-
**Module.Basis.dualBasis_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：dualBasis_apply (i : ι) (m : M) : b.dualBasis i m = b.repr m i
参数：i : ι；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.toDual_apply_right`：toDual_apply_right (i : ι) (m : M) : b.
toDual (b i) m = b.repr m i
-/
theorem dualBasis_apply (i : ι) (m : M) : b.dualBasis i m = b.repr m i :=
  b.toDual_apply_right i m

@[simp]
/-
**Module.Basis.coe_dualBasis** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_dualBasis : ⇑b.dualBasis = b.coord
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Module.Basis.dualBasis_apply`：dualBasis_apply (i : ι) (m : M) : b.dualBa
sis i m = b.repr m i
-/
theorem coe_dualBasis : ⇑b.dualBasis = b.coord := by
  ext i x
  apply dualBasis_apply

@[simp]
/-
**Module.Basis.toDual_toDual** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：toDual_toDual : b.dualBasis.toDual.comp b.toDual = Dual.eval R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `Module.Basis.toDual_apply_left`：toDual_apply_left (m : M) (i : ι) : b.to
Dual m (b i) = b.repr m i
· 使用定理 `Module.Basis.coe_toDual_self`：coe_toDual_self (i : ι) : b.toDual (b i) =
 b.coord i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.coe_dualBasis`：coe_dualBasis : ⇑b.dualBasis = b.coord
· 使用定理 `Module.Dual.eval_apply`：eval_apply (v : M) (a : Dual R M) : eval R M v a
 = a v
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Module.Basis.dualBasis_apply_self`：dualBasis_apply_self (i j : ι) : b.du
alBasis i (b j) = if j = i then 1 else 0
-/
theorem toDual_toDual : b.dualBasis.toDual.comp b.toDual = Dual.eval R M := by
  refine b.ext fun i => b.dualBasis.ext fun j => ?_
  rw [LinearMap.comp_apply, toDual_apply_left, coe_toDual_self, ← coe_dualBasis,
    Dual.eval_apply, Basis.repr_self, Finsupp.single_apply, dualBasis_apply_self]

end Finite

/-
**Module.Basis.dualBasis_equivFun** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：dualBasis_equivFun [Finite ι] (l : Dual R M) (i : ι) : b.dualBasis.equivFu
n l i = l (b i)
参数：l : Dual R M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.equivFun_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u
_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] [inst_3 : Finit…
· 使用定理 `Module.Basis.dualBasis_repr`：∀ {R : Type uR} {M : Type uM} {ι : Type uι}
 [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R 
M] [inst_3 : Deci…
-/
theorem dualBasis_equivFun [Finite ι] (l : Dual R M) (i : ι) :
    b.dualBasis.equivFun l i = l (b i) := by rw [Basis.equivFun_apply, dualBasis_repr]
/-
**Module.Basis.eval_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：eval_injective {ι : Type*} (b : Basis ι R M) : Function.Injective (Dual.ev
al R M)
参数：b : Basis ι R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.Basis.ext_elem`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_12}
 [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (
b : Module.…
-/
theorem eval_injective {ι : Type*} (b : Basis ι R M) : Function.Injective (Dual.eval R M) := by
  intro m m' eq
  simp_rw [LinearMap.ext_iff, Dual.eval_apply] at eq
  exact b.ext_elem fun i ↦ eq (b.coord i)
/-
**Module.Basis.eval_ker** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：eval_ker {ι : Type*} (b : Basis ι R M) : LinearMap.ker (Dual.eval R M) = ⊥
参数：b : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.Basis.eval_injective`：eval_injective {ι : Type*} (b : Basis ι R M
) : Function.Injective (Dual.eval R M)
-/
theorem eval_ker {ι : Type*} (b : Basis ι R M) : LinearMap.ker (Dual.eval R M) = ⊥ :=
  ker_eq_bot_of_injective (eval_injective b)
/-
**Module.Basis.eval_range** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：eval_range {ι : Type*} [Finite ι] (b : Basis ι R M) : LinearMap.range (Dua
l.eval R M) = ⊤
参数：b : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.toDual_toDual`：toDual_toDual : b.dualBasis.toDual.comp b.to
Dual = Dual.eval R M
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Module.Basis.toDual_range`：toDual_range [Finite ι] : LinearMap.range b.t
oDual = ⊤
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
-/
theorem eval_range {ι : Type*} [Finite ι] (b : Basis ι R M) :
    LinearMap.range (Dual.eval R M) = ⊤ := by
  classical
    cases nonempty_fintype ι
    rw [← b.toDual_toDual, range_comp, b.toDual_range, Submodule.map_top, toDual_range _]
/-
**Module.Basis.dualBasis_coord_toDualEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Modu
le.Basis`。
形式化陈述：dualBasis_coord_toDualEquiv_apply [Finite ι] (i : ι) (f : M) : b.dualBasis
.coord i (b.toDualEquiv f) = b.coord i f
参数：i : ι；f : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.map_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M
' : Type u_7} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M]…
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dualBasis_coord_toDualEquiv_apply [Finite ι] (i : ι) (f : M) :
    b.dualBasis.coord i (b.toDualEquiv f) = b.coord i f := by
  simp [-toDualEquiv_apply, Basis.dualBasis]
/-
**Module.Basis.coord_toDualEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Module.Ba
sis`。
形式化陈述：coord_toDualEquiv_symm_apply [Finite ι] (i : ι) (f : Module.Dual R M) : b.
coord i (b.toDualEquiv.symm f) = b.dualBasis.coord i f
参数：i : ι；f : Module.Dual R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.map_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M
' : Type u_7} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coord_toDualEquiv_symm_apply [Finite ι] (i : ι) (f : Module.Dual R M) :
    b.coord i (b.toDualEquiv.symm f) = b.dualBasis.coord i f := by
  simp [Basis.dualBasis]

omit [DecidableEq ι]

/-- `simp` normal form version of `linearCombination_dualBasis` -/
@[simp]
/-
**Module.Basis.linearCombination_coord** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：linearCombination_coord [Finite ι] (b : Basis ι R M) (f : ι ->₀ R) (i : ι)
 : Finsupp.linearCombination R b.coord f (b i) = f i
参数：b : Basis ι R M；f : ι ->₀ R；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.coe_dualBasis`：coe_dualBasis : ⇑b.dualBasis = b.coord
· 使用定理 `Module.Basis.linearCombination_dualBasis`：linearCombination_dualBasis (f
 : ι ->₀ R) (i : ι) : Finsupp.linearCombination R b.dualBasis f (b i) = f i

--- 原说明 ---
`simp` normal form version of `linearCombination_dualBasis`
-/
theorem linearCombination_coord [Finite ι] (b : Basis ι R M) (f : ι →₀ R) (i : ι) :
    Finsupp.linearCombination R b.coord f (b i) = f i := by
  have := Classical.decEq ι
  rw [← coe_dualBasis, linearCombination_dualBasis]

end CommSemiring

end Module.Basis

section DualBases

variable {R M ι : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

open Lean.Elab.Tactic in
/-- Try using `Set.toFinite` to dispatch a `Set.Finite` goal. -/
meta def evalUseFiniteInstance : TacticM Unit := do
  evalTactic (← `(tactic| intros; apply Set.toFinite))

@[inherit_doc evalUseFiniteInstance]
elab "use_finite_instance" : tactic => evalUseFiniteInstance

/-- `e` and `ε` have characteristic properties of a basis and its dual -/
/-
**Module.DualBases** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：Module.DualBases (e : ι -> M) (ε : ι -> Dual R M) : Prop where eval_same :
 forall i, ε i (e i) = 1 eval_of_ne : Pairwise fun i j => ε i (e j) = 0 protecte
d total : forall {m₁ m₂ : M}, (forall i, ε i m₁ = ε i m₂) -> m₁ = m₂ protected f
inite : forall m : M, {i | ε i m != 0}.Finite
参数：e : ι -> M；ε : ι -> Dual R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`e` and `ε` have characteristic properties of a basis and its dual
-/
structure Module.DualBases (e : ι → M) (ε : ι → Dual R M) : Prop where
  eval_same : ∀ i, ε i (e i) = 1
  eval_of_ne : Pairwise fun i j ↦ ε i (e j) = 0
  protected total : ∀ {m₁ m₂ : M}, (∀ i, ε i m₁ = ε i m₂) → m₁ = m₂
  protected finite : ∀ m : M, {i | ε i m ≠ 0}.Finite := by use_finite_instance

end DualBases

namespace Module.DualBases

open LinearMap Function

variable {R M ι : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {e : ι → M} {ε : ι → Dual R M}

/-- The coefficients of `v` on the basis `e` -/
/-
**Module.DualBases.coeffs** 是 Mathlib 中的一个定义，位于命名空间 `Module.DualBases`。
形式化陈述：coeffs (h : DualBases e ε) (m : M) : ι ->₀ R where toFun i
参数：h : DualBases e ε；m : M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DualBases.finite`：∀ {R : Type u_1} {M : Type u_2} {ι : Type u_3} 
[inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] {e : ι → M}…

--- 原说明 ---
The coefficients of `v` on the basis `e`
-/
def coeffs (h : DualBases e ε) (m : M) : ι →₀ R where
  toFun i := ε i m
  support := (h.finite m).toFinset
  mem_support_toFun i := by rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

@[simp]
/-
**Module.DualBases.coeffs_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.DualBases`。
形式化陈述：coeffs_apply (h : DualBases e ε) (m : M) (i : ι) : h.coeffs m i = ε i m
参数：h : DualBases e ε；m : M；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeffs_apply (h : DualBases e ε) (m : M) (i : ι) : h.coeffs m i = ε i m :=
  rfl

/-- linear combinations of elements of `e`.
This is a convenient abbreviation for `Finsupp.linearCombination R e l` -/
/-
**Module.DualBases.lc** 是 Mathlib 中的一个定义，位于命名空间 `Module.DualBases`。
形式化陈述：lc {ι} (e : ι -> M) (l : ι ->₀ R) : M
参数：e : ι -> M；l : ι ->₀ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
linear combinations of elements of `e`.
This is a convenient abbreviation for `Finsupp.linearCombination R e l`
-/
def lc {ι} (e : ι → M) (l : ι →₀ R) : M :=
  l.sum fun (i : ι) (a : R) => a • e i
/-
**Module.DualBases.lc_def** 是 Mathlib 中的一个定理，位于命名空间 `Module.DualBases`。
形式化陈述：lc_def (e : ι -> M) (l : ι ->₀ R) : lc e l = Finsupp.linearCombination R e
 l
参数：e : ι -> M；l : ι ->₀ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lc_def (e : ι → M) (l : ι →₀ R) : lc e l = Finsupp.linearCombination R e l :=
  rfl

open Module

variable (h : DualBases e ε)
include h
/-
**Module.DualBases.dual_lc** 是 Mathlib 中的一个定理，位于命名空间 `Module.DualBases`。
形式化陈述：dual_lc (l : ι ->₀ R) (i : ι) : ε i (DualBases.lc e l) = l i
参数：l : ι ->₀ R；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.DualBases.lc.eq_1`：∀ {R : Type u_1} {M : Type u_2} [inst : CommSe
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {ι : Type u_
4} (e : ι → M)…
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finsupp.sum_eq_single`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M} (a : α)   {g : α → M → N}
, (∀ (b : α…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Module.DualBases.eval_of_ne`：∀ {R : Type u_1} {M : Type u_2} {ι : Type u
_3} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module
 R M] {e : ι → M}…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Module.DualBases.eval_same`：∀ {R : Type u_1} {M : Type u_2} {ι : Type u_
3} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] {e : ι → M}…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem dual_lc (l : ι →₀ R) (i : ι) : ε i (DualBases.lc e l) = l i := by
  rw [lc, map_finsuppSum, Finsupp.sum_eq_single i (g := fun a b ↦ (ε i) (b • e a))]
  · simp [h.eval_same, smul_eq_mul]
  · intro q _ q_ne
    simp [h.eval_of_ne q_ne.symm, smul_eq_mul]
  · simp

@[simp]
/-
**Module.DualBases.coeffs_lc** 是 Mathlib 中的一个定理，位于命名空间 `Module.DualBases`。
形式化陈述：coeffs_lc (l : ι ->₀ R) : h.coeffs (DualBases.lc e l) = l
参数：l : ι ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.DualBases.coeffs_apply`：coeffs_apply (h : DualBases e ε) (m : M) 
(i : ι) : h.coeffs m i = ε i m
· 使用定理 `Module.DualBases.dual_lc`：dual_lc (l : ι ->₀ R) (i : ι) : ε i (DualBases
.lc e l) = l i
-/
theorem coeffs_lc (l : ι →₀ R) : h.coeffs (DualBases.lc e l) = l := by
  ext i
  rw [h.coeffs_apply, h.dual_lc]

/-- For any `m : M n`, $\sum_{p ∈ Q n} (ε p m) • e p = m$ -/
@[simp]
/-
**Module.DualBases.lc_coeffs** 是 Mathlib 中的一个定理，位于命名空间 `Module.DualBases`。
形式化陈述：lc_coeffs (m : M) : DualBases.lc e (h.coeffs m) = m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DualBases.total`：∀ {R : Type u_1} {M : Type u_2} {ι : Type u_3} [
inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M]
 {e : ι → M}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.DualBases.dual_lc`：dual_lc (l : ι ->₀ R) (i : ι) : ε i (DualBases
.lc e l) = l i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
For any `m : M n`, $\sum_{p ∈ Q n} (ε p m) • e p = m$
-/
theorem lc_coeffs (m : M) : DualBases.lc e (h.coeffs m) = m := h.total <| by simp [h.dual_lc]

/-- `(h : DualBases e ε).basis` shows the family of vectors `e` forms a basis. -/
@[simps repr_apply, simps -isSimp repr_symm_apply]
/-
**Module.DualBases.basis** 是 Mathlib 中的一个定义，位于命名空间 `Module.DualBases`。
形式化陈述：basis : Basis ι R M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DualBases.lc_coeffs`：lc_coeffs (m : M) : DualBases.lc e (h.coeffs
 m) = m
· 使用定理 `Module.DualBases.coeffs_lc`：coeffs_lc (l : ι ->₀ R) : h.coeffs (DualBase
s.lc e l) = l

--- 原说明 ---
`(h : DualBases e ε).basis` shows the family of vectors `e` forms a basis.
-/
def basis : Basis ι R M :=
  Basis.ofRepr
    { toFun := coeffs h
      invFun := lc e
      left_inv := lc_coeffs h
      right_inv := coeffs_lc h
      map_add' := fun v w => by
        ext i
        exact (ε i).map_add v w
      map_smul' := fun c v => by
        ext i
        exact (ε i).map_smul c v }

@[simp]
/-
**Module.DualBases.coe_basis** 是 Mathlib 中的一个定理，位于命名空间 `Module.DualBases`。
形式化陈述：coe_basis : ⇑h.basis = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.apply_eq_iff`：apply_eq_iff {b : Basis ι R M} {x : M} {i : ι
} : b i = x ↔ b.repr x = Finsupp.single i 1
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.DualBases.basis_repr_apply`：∀ {R : Type u_1} {M : Type u_2} {ι : 
Type u_3} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M] {e : ι → M}…
· 使用定理 `Module.DualBases.eval_same`：∀ {R : Type u_1} {M : Type u_2} {ι : Type u_
3} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] {e : ι → M}…
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.DualBases.eval_of_ne`：∀ {R : Type u_1} {M : Type u_2} {ι : Type u
_3} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module
 R M] {e : ι → M}…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem coe_basis : ⇑h.basis = e := by
  ext i
  rw [Basis.apply_eq_iff]
  ext j
  rcases eq_or_ne i j with rfl | hne
  · simp [h.eval_same]
  · simp [hne, h.eval_of_ne hne.symm]
/-
**Module.DualBases.mem_of_mem_span** 是 Mathlib 中的一个定理，位于命名空间 `Module.DualBases`。
形式化陈述：mem_of_mem_span {H : Set ι} {x : M} (hmem : x in Submodule.span R (e '' H)
) : forall i : ι, ε i x != 0 -> i in H
参数：hmem : x in Submodule.span R (e '' H)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_span_image_iff_linearCombination`：mem_span_image_iff_linearC
ombination {s : Set α} {x : M} : x in span R (v '' s) ↔ exists l in supported R 
R s, linearCombination R v l = x
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `Finsupp.mem_supported'`：mem_supported' {s : Set α} (p : α ->₀ M) : p in 
supported M R s ↔ forall x ∉ s, p x = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.DualBases.dual_lc`：dual_lc (l : ι ->₀ R) (i : ι) : ε i (DualBases
.lc e l) = l i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.DualBases.lc_def`：lc_def (e : ι -> M) (l : ι ->₀ R) : lc e l = Fi
nsupp.linearCombination R e l
-/
theorem mem_of_mem_span {H : Set ι} {x : M} (hmem : x ∈ Submodule.span R (e '' H)) :
    ∀ i : ι, ε i x ≠ 0 → i ∈ H := by
  intro i hi
  rcases (Finsupp.mem_span_image_iff_linearCombination _).mp hmem with ⟨l, supp_l, rfl⟩
  apply not_imp_comm.mp ((Finsupp.mem_supported' _ _).mp supp_l i)
  rwa [← lc_def, h.dual_lc] at hi
/-
**Module.DualBases.coe_dualBasis** 是 Mathlib 中的一个定理，位于命名空间 `Module.DualBases`。
形式化陈述：coe_dualBasis [DecidableEq ι] [Finite ι] : ⇑h.basis.dualBasis = ε
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_dualBasis`：coe_dualBasis : ⇑b.dualBasis = b.coord
· 使用定理 `Module.DualBases.coe_basis`：coe_basis : ⇑h.basis = e
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.DualBases.basis_repr_apply`：∀ {R : Type u_1} {M : Type u_2} {ι : 
Type u_3} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M] {e : ι → M}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_dualBasis [DecidableEq ι] [Finite ι] : ⇑h.basis.dualBasis = ε :=
  funext fun i => h.basis.ext fun j => by simp

end Module.DualBases

