/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Matrix algebra is an Azumaya algebra over R

In this file we prove that finite-dimensional matrix algebra `Matrix n n R` over `R`
is an Azumaya algebra where `R` is a commutative ring.

## Main Results

- `IsAzumaya.Matrix`: Finite-dimensional matrix algebra over `R` is Azumaya.

-/

public section
open scoped TensorProduct

variable (R n : Type*) [CommSemiring R] [Fintype n] [DecidableEq n]

noncomputable section

open Matrix MulOpposite

/-- `AlgHom.mulLeftRight` for matrix algebra sends basis Eᵢⱼ⊗Eₖₗ to
  the map `f : Eₛₜ ↦ Eᵢⱼ * Eₛₜ * Eₖₗ = δⱼₛδₜₖEᵢₗ`, therefore we construct the inverse
  by sending `f` to `∑ᵢₗₛₜ f(Eₛₜ)ᵢₗ • Eᵢₛ⊗Eₜₗ`. -/
/-
**AlgHom.mulLeftRightMatrix_inv** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AlgHom.mulLeftRightMatrix_inv : Module.End R (Matrix n n R) ->ₗ[R] Matrix 
n n R otimes[R] (Matrix n n R)ᵐᵒᵖ where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgHom.mulLeftRight` for matrix algebra sends basis Eᵢⱼ⊗Eₖₗ to
  the map `f : Eₛₜ ↦ Eᵢⱼ * Eₛₜ * Eₖₗ = δⱼₛδₜₖEᵢₗ`, therefore we construct the in
verse
  by sending `f` to `∑ᵢₗₛₜ f(Eₛₜ)ᵢₗ • Eᵢₛ⊗Eₜₗ`.
-/
abbrev AlgHom.mulLeftRightMatrix_inv :
    Module.End R (Matrix n n R) →ₗ[R] Matrix n n R ⊗[R] (Matrix n n R)ᵐᵒᵖ where
  toFun f := ∑ ⟨⟨i, j⟩, k, l⟩ : (n × n) × n × n,
    f (single j k 1) i l • (single i j 1) ⊗ₜ[R] op (single k l 1)
  map_add' f1 f2 := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r f := by simp [mul_smul, Finset.smul_sum]
/-
**AlgHom.mulLeftRightMatrix.inv_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgHom.mulLeftRightMatrix.inv_comp : (AlgHom.mulLeftRightMatrix_inv R n).c
omp (AlgHom.mulLeftRight R (Matrix n n R)).toLinearMap = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.tensorProduct_apply`：tensorProduct_apply (b : Basis ι S M) 
(c : Basis κ R N) (i : ι) (j : κ) : tensorProduct b c (i, j) = b i otimesₜ c j
· 使用定理 `Matrix.stdBasis_eq_single`：stdBasis_eq_single (i : m) (j : n) [Decidable
Eq m] [DecidableEq n] : stdBasis R m n (i, j) = single i j (1 : R)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_and`：ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fintype.sum_prod_type`：∀ {γ : Type u_3} {α₁ : Type u_4} {α₂ : Type u_5} 
[inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid γ]   (f : α₁ ×
 α₂ → γ), ∑…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用引理 `AlgHom.mulLeftRight_apply`：AlgHom.mulLeftRight_apply (a : A) (b : Aᵐᵒᵖ) 
(x : A) : AlgHom.mulLeftRight R A (a otimesₜ b) x = a * x * b.unop
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `Finset.sum_ite_irrel`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMon
oid M] (p : Prop) [inst_1 : Decidable p] (s : Finset ι) (f g : ι → M),   (∑ x ∈ 
s, if p th…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
（共 31 条，此处仅展示前 30 条）
-/
lemma AlgHom.mulLeftRightMatrix.inv_comp :
    (AlgHom.mulLeftRightMatrix_inv R n).comp
    (AlgHom.mulLeftRight R (Matrix n n R)).toLinearMap = .id :=
  ((Matrix.stdBasis _ _ _).tensorProduct ((Matrix.stdBasis _ _ _).map (opLinearEquiv ..))).ext
  fun ⟨⟨i0, j0⟩, k0, l0⟩ ↦ by
    simp [stdBasis_eq_single, ite_and, Fintype.sum_prod_type,
      mulLeftRight_apply, single, Matrix.mul_apply]
/-
**AlgHom.mulLeftRightMatrix.comp_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgHom.mulLeftRightMatrix.comp_inv : (AlgHom.mulLeftRight R (Matrix n n R)
).toLinearMap.comp (AlgHom.mulLeftRightMatrix_inv R n) = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Matrix.stdBasis_eq_single`：stdBasis_eq_single (i : m) (j : n) [Decidable
Eq m] [DecidableEq n] : stdBasis R m n (i, j) = single i j (1 : R)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_and`：ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b
· 使用引理 `AlgHom.mulLeftRight_apply`：AlgHom.mulLeftRight_apply (a : A) (b : Aᵐᵒᵖ) 
(x : A) : AlgHom.mulLeftRight R A (a otimesₜ b) x = a * x * b.unop
· 使用定理 `Matrix.sum_apply`：sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finse
t β) (g : β -> Matrix m n α) : (∑ c in s, g c) i j = ∑ c in s, g c i j
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
（共 36 条，此处仅展示前 30 条）
-/
lemma AlgHom.mulLeftRightMatrix.comp_inv :
    (AlgHom.mulLeftRight R (Matrix n n R)).toLinearMap.comp
    (AlgHom.mulLeftRightMatrix_inv R n) = .id := by
  ext f : 1
  apply (Matrix.stdBasis _ _ _).ext
  intro ⟨i, j⟩
  simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, map_sum,
    map_smul, stdBasis_eq_single, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  ext k l
  simp [sum_apply, Matrix.mul_apply, single, Fintype.sum_prod_type, ite_and]

namespace IsAzumaya

/-- A nontrivial matrix ring over `R` is an Azumaya algebra over `R`. -/
/-
**IsAzumaya.matrix** 是 Mathlib 中的一个定理，位于命名空间 `IsAzumaya`。
形式化陈述：matrix [Nonempty n] : IsAzumaya R (Matrix n n R) where eq_of_smul_eq_smul
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `AlgHom.mulLeftRightMatrix.inv_comp`：AlgHom.mulLeftRightMatrix.inv_comp :
 (AlgHom.mulLeftRightMatrix_inv R n).comp (AlgHom.mulLeftRight R (Matrix n n R))
.toLinearMap = .id
· 使用引理 `AlgHom.mulLeftRightMatrix.comp_inv`：AlgHom.mulLeftRightMatrix.comp_inv :
 (AlgHom.mulLeftRight R (Matrix n n R)).toLinearMap.comp (AlgHom.mulLeftRightMat
rix_inv R n) = .id

--- 原说明 ---
A nontrivial matrix ring over `R` is an Azumaya algebra over `R`.
-/
theorem matrix [Nonempty n] : IsAzumaya R (Matrix n n R) where
  eq_of_smul_eq_smul := by nontriviality R; exact eq_of_smul_eq_smul
  bij := Function.bijective_iff_has_inverse.mpr
    ⟨AlgHom.mulLeftRightMatrix_inv R n,
    DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.inv_comp R n),
    DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.comp_inv R n)⟩

end IsAzumaya

end

