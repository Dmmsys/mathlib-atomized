/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Lemmas about bilinear maps with a basis over each argument
-/

public section

open Module

namespace LinearMap

variable {ι₁ ι₂ : Type*}
variable {R R₂ S S₂ M N P Rₗ : Type*}
variable {Mₗ Nₗ Pₗ : Type*}

-- Could weaken [CommSemiring Rₗ] to [SMulCommClass Rₗ Rₗ Pₗ], but might impact performance
variable [Semiring R] [Semiring S] [Semiring R₂] [Semiring S₂] [CommSemiring Rₗ]

section AddCommMonoid

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [AddCommMonoid Mₗ] [AddCommMonoid Nₗ] [AddCommMonoid Pₗ]
variable [Module R M] [Module S N] [Module R₂ P] [Module S₂ P]
variable [Module Rₗ Mₗ] [Module Rₗ Nₗ] [Module Rₗ Pₗ]
variable [SMulCommClass S₂ R₂ P]
variable {ρ₁₂ : R →+* R₂} {σ₁₂ : S →+* S₂}
variable (b₁ : Basis ι₁ R M) (b₂ : Basis ι₂ S N) (b₁' : Basis ι₁ Rₗ Mₗ) (b₂' : Basis ι₂ Rₗ Nₗ)

/-- Two bilinear maps are equal when they are equal on all basis vectors. -/
/-
**LinearMap.ext_basis** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ext_basis {B B' : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (h : forall i j, B (b₁ i) (b₂
 j) = B' (b₁ i) (b₂ j)) : B = B'
参数：h : forall i j, B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂

--- 原说明 ---
Two bilinear maps are equal when they are equal on all basis vectors.
-/
theorem ext_basis {B B' : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (h : ∀ i j, B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j)) :
    B = B' :=
  b₁.ext fun i => b₂.ext fun j => h i j
/-
**LinearMap.ext_iff_basis** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：ext_iff_basis {B B' : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} : B = B' ↔ forall (i : ι₁
) (j : ι₂), B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext_basis`：ext_basis {B B' : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (h : f
orall i j, B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j)) : B = B'
-/
lemma ext_iff_basis {B B' : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} :
    B = B' ↔ ∀ (i : ι₁) (j : ι₂), B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j) :=
  ⟨fun h _ _ ↦ h ▸ rfl, ext_basis b₁ b₂⟩
/-
**LinearMap.BilinForm.ext_iff_basis** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFo
rm`。
形式化陈述：∀ {ι₁ : Type u_1} {Rₗ : Type u_10} {Mₗ : Type u_11} [inst : CommSemiring R
ₗ] [inst_1 : AddCommMonoid Mₗ]   [inst_2 : _root_.Module Rₗ Mₗ] (b₁' : Module.Ba
sis ι₁ Rₗ Mₗ) {B B' : LinearMap.BilinForm Rₗ Mₗ},   B = B' ↔ ∀ (i j : ι₁), (B (b
₁' i)) (b₁' j) = (B' (b₁' i)) (b₁' j)
参数：b₁' : Module.Basis ι₁ Rₗ Mₗ；i j : ι₁；B (b₁' i)；b₁' j；B' (b₁' i)；b₁' j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.ext_iff_basis`：ext_iff_basis {B B' : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P
} : B = B' ↔ forall (i : ι₁) (j : ι₂), B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j)
-/
lemma BilinForm.ext_iff_basis {B B' : LinearMap.BilinForm Rₗ Mₗ} :
    B = B' ↔ ∀ (i j : ι₁), B (b₁' i) (b₁' j) = B' (b₁' i) (b₁' j) :=
  LinearMap.ext_iff_basis b₁' b₁'

/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis.

Version for semi-bilinear maps, see `sum_repr_mul_repr_mul` for the bilinear version. -/
/-
**LinearMap.sum_repr_mul_repr_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：sum_repr_mul_repr_mul {B : Mₗ ->ₗ[Rₗ] Nₗ ->ₗ[Rₗ] Pₗ} (x y) : ((b₁'.repr x)
.sum fun i xi => (b₂'.repr y).sum fun j yj => xi • yj • B (b₁' i) (b₂' j)) = B x
 y
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LinearMap.map_sum₂`：map_sum₂ {ι : Type*} (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P)
 (t : Finset ι) (x : ι -> M) (y) : f (∑ i in t, x i) y = ∑ i in t, f (x i) y
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.map_smul₂`：map_smul₂ (f : M₂ ->ₗ[R] N₂ ->ₛₗ[σ₁₂] P₂) (r : R) (
x y) : f (r • x) y = r • f x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis.

Version for semi-bilinear maps, see `sum_repr_mul_repr_mul` for the bilinear ver
sion.
-/
theorem sum_repr_mul_repr_mulₛₗ {B : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (x y) :
    ((b₁.repr x).sum fun i xi => (b₂.repr y).sum fun j yj => ρ₁₂ xi • σ₁₂ yj • B (b₁ i) (b₂ j)) =
      B x y := by
  conv_rhs => rw [← b₁.linearCombination_repr x, ← b₂.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂, map_sum, map_smulₛₗ₂, map_smulₛₗ]

set_option backward.isDefEq.respectTransparency false in
/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis.

Version for bilinear maps, see `sum_repr_mul_repr_mulₛₗ` for the semi-bilinear version. -/
/-
**LinearMap.sum_repr_mul_repr_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：sum_repr_mul_repr_mul {B : Mₗ ->ₗ[Rₗ] Nₗ ->ₗ[Rₗ] Pₗ} (x y) : ((b₁'.repr x)
.sum fun i xi => (b₂'.repr y).sum fun j yj => xi • yj • B (b₁' i) (b₂' j)) = B x
 y
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LinearMap.map_sum₂`：map_sum₂ {ι : Type*} (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P)
 (t : Finset ι) (x : ι -> M) (y) : f (∑ i in t, x i) y = ∑ i in t, f (x i) y
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.map_smul₂`：map_smul₂ (f : M₂ ->ₗ[R] N₂ ->ₛₗ[σ₁₂] P₂) (r : R) (
x y) : f (r • x) y = r • f x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis.

Version for bilinear maps, see `sum_repr_mul_repr_mulₛₗ` for the semi-bilinear v
ersion.
-/
theorem sum_repr_mul_repr_mul {B : Mₗ →ₗ[Rₗ] Nₗ →ₗ[Rₗ] Pₗ} (x y) :
    ((b₁'.repr x).sum fun i xi => (b₂'.repr y).sum fun j yj => xi • yj • B (b₁' i) (b₂' j)) =
      B x y := by
  conv_rhs => rw [← b₁'.linearCombination_repr x, ← b₂'.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂, map_sum, map_smul₂, map_smul]

end AddCommMonoid

end LinearMap

