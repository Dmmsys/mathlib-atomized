/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.Finsupp.SumProd

/-!
# Results on finitely supported functions.

* `TensorProduct.finsuppLeft`, the tensor product of `ι →₀ M` and `N`
  is linearly equivalent to `ι →₀ M ⊗[R] N`

* `TensorProduct.finsuppScalarLeft`, the tensor product of `ι →₀ R` and `N`
  is linearly equivalent to `ι →₀ N`

* `TensorProduct.finsuppRight`, the tensor product of `M` and `ι →₀ N`
  is linearly equivalent to `ι →₀ M ⊗[R] N`

* `TensorProduct.finsuppScalarRight`, the tensor product of `M` and `ι →₀ R`
  is linearly equivalent to `ι →₀ N`

* `TensorProduct.finsuppLeft'`, if `M` is an `S`-module,
  then the tensor product of `ι →₀ M` and `N` is `S`-linearly equivalent
  to `ι →₀ M ⊗[R] N`

* `finsuppTensorFinsupp`, the tensor product of `ι →₀ M` and `κ →₀ N`
  is linearly equivalent to `(ι × κ) →₀ (M ⊗ N)`.

-/

@[expose] public section


noncomputable section

open DirectSum TensorProduct

open Set LinearMap Submodule

section TensorProduct

variable (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S]
  (M : Type*) [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  (N : Type*) [AddCommMonoid N] [Module R N]

namespace TensorProduct

variable (ι : Type*) [DecidableEq ι]

/-- The tensor product of `ι →₀ M` and `N` is linearly equivalent to `ι →₀ M ⊗[R] N` -/
/-
**TensorProduct.finsuppLeft** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：finsuppLeft : (ι ->₀ M) otimes[R] N ≃ₗ[S] ι ->₀ M otimes[R] N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
The tensor product of `ι →₀ M` and `N` is linearly equivalent to `ι →₀ M ⊗[R] N`
-/
noncomputable def finsuppLeft :
    (ι →₀ M) ⊗[R] N ≃ₗ[S] ι →₀ M ⊗[R] N :=
  AlgebraTensorModule.congr (finsuppLEquivDirectSum S M ι) (.refl R N) ≪≫ₗ
    directSumLeft _ S (fun _ ↦ M) N ≪≫ₗ (finsuppLEquivDirectSum _ _ ι).symm

variable {R S M N ι}
/-
**TensorProduct.finsuppLeft_apply_tmul** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`
。
形式化陈述：finsuppLeft_apply_tmul (p : ι ->₀ M) (n : N) : finsuppLeft R S M N ι (p ot
imesₜ[R] n) = p.sum fun i m => Finsupp.single i (m otimesₜ[R] n)
参数：p : ι ->₀ M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.induction_linear`：induction_linear {motive : (ι ->₀ M) -> Prop} 
(f : ι ->₀ M) (zero : motive 0) (add : forall f g : ι ->₀ M, motive f -> motive 
g -> motive (f…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Finsupp.sum_add_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : DecidableEq α] [inst_1 : AddZeroClass M]   [inst_2 : AddCommMonoid N] {f 
g : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `finsuppLEquivDirectSum_single`：finsuppLEquivDirectSum_single (i : ι) (m 
: M) : finsuppLEquivDirectSum R M ι (Finsupp.single i m) = DirectSum.lof R ι _ i
 m
· 使用定理 `TensorProduct.directSumLeft_tmul_lof`：directSumLeft_tmul_lof (i : ι₁) (x
 : M₁ i) (y : M₂') : directSumLeft R S M₁ M₂' (DirectSum.lof S _ _ i x otimesₜ[R
] y) = DirectSum.lof S _ _…
· 使用定理 `finsuppLEquivDirectSum_symm_lof`：finsuppLEquivDirectSum_symm_lof (i : ι)
 (m : M) : (finsuppLEquivDirectSum R M ι).symm (DirectSum.lof R ι _ i m) = Finsu
pp.single i m
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
-/
lemma finsuppLeft_apply_tmul (p : ι →₀ M) (n : N) :
    finsuppLeft R S M N ι (p ⊗ₜ[R] n) = p.sum fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [add_tmul, map_add, hf, hg, Finsupp.sum_add_index]
  | single => simp [finsuppLeft]

@[simp]
/-
**TensorProduct.finsuppLeft_apply_tmul_apply** 是 Mathlib 中的一个引理，位于命名空间 `TensorPr
oduct`。
形式化陈述：finsuppLeft_apply_tmul_apply (p : ι ->₀ M) (n : N) (i : ι) : finsuppLeft R
 S M N ι (p otimesₜ[R] n) i = p i otimesₜ[R] n
参数：p : ι ->₀ M；n : N；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.finsuppLeft_apply_tmul`：finsuppLeft_apply_tmul (p : ι ->₀ 
M) (n : N) : finsuppLeft R S M N ι (p otimesₜ[R] n) = p.sum fun i m => Finsupp.s
ingle i (m otimesₜ[R] n)
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Finsupp.sum_eq_single`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M} (a : α)   {g : α → M → N}
, (∀ (b : α…
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
lemma finsuppLeft_apply_tmul_apply (p : ι →₀ M) (n : N) (i : ι) :
    finsuppLeft R S M N ι (p ⊗ₜ[R] n) i = p i ⊗ₜ[R] n := by
  rw [finsuppLeft_apply_tmul, Finsupp.sum_apply,
    Finsupp.sum_eq_single i (fun _ _ ↦ Finsupp.single_eq_of_ne') (by simp), Finsupp.single_eq_same]
/-
**TensorProduct.finsuppLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：finsuppLeft_apply (t : (ι ->₀ M) otimes[R] N) (i : ι) : finsuppLeft R S M 
N ι t i = rTensor N (Finsupp.lapply i) t
参数：t : (ι ->₀ M) otimes[R] N；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `TensorProduct.finsuppLeft_apply_tmul_apply`：finsuppLeft_apply_tmul_apply
 (p : ι ->₀ M) (n : N) (i : ι) : finsuppLeft R S M N ι (p otimesₜ[R] n) i = p i 
otimesₜ[R] n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem finsuppLeft_apply (t : (ι →₀ M) ⊗[R] N) (i : ι) :
    finsuppLeft R S M N ι t i = rTensor N (Finsupp.lapply i) t := by
  induction t with
  | zero => simp
  | tmul f n => simp only [finsuppLeft_apply_tmul_apply, rTensor_tmul, Finsupp.lapply_apply]
  | add x y hx hy => simp [map_add, hx, hy]

@[simp]
/-
**TensorProduct.finsuppLeft_symm_apply_single** 是 Mathlib 中的一个引理，位于命名空间 `TensorP
roduct`。
形式化陈述：finsuppLeft_symm_apply_single (i : ι) (m : M) (n : N) : (finsuppLeft R S M
 N ι).symm (Finsupp.single i (m otimesₜ[R] n)) = Finsupp.single i m otimesₜ[R] n
参数：i : ι；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsuppLEquivDirectSum_single`：finsuppLEquivDirectSum_single (i : ι) (m 
: M) : finsuppLEquivDirectSum R M ι (Finsupp.single i m) = DirectSum.lof R ι _ i
 m
· 使用定理 `TensorProduct.directSumLeft_symm_lof_tmul`：directSumLeft_symm_lof_tmul (
i : ι₁) (x : M₁ i) (y : M₂') : (directSumLeft R S M₁ M₂').symm (DirectSum.lof S 
_ _ i (x otimesₜ[R] y)) = Direc…
· 使用定理 `finsuppLEquivDirectSum_symm_lof`：finsuppLEquivDirectSum_symm_lof (i : ι)
 (m : M) : (finsuppLEquivDirectSum R M ι).symm (DirectSum.lof R ι _ i m) = Finsu
pp.single i m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finsuppLeft_symm_apply_single (i : ι) (m : M) (n : N) :
    (finsuppLeft R S M N ι).symm (Finsupp.single i (m ⊗ₜ[R] n)) =
      Finsupp.single i m ⊗ₜ[R] n := by
  simp [finsuppLeft]

variable (R S M N ι) in
/-- The tensor product of `M` and `ι →₀ N` is linearly equivalent to `ι →₀ M ⊗[R] N` -/
/-
**TensorProduct.finsuppRight** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：finsuppRight : M otimes[R] (ι ->₀ N) ≃ₗ[S] ι ->₀ M otimes[R] N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
The tensor product of `M` and `ι →₀ N` is linearly equivalent to `ι →₀ M ⊗[R] N`
-/
noncomputable def finsuppRight :
    M ⊗[R] (ι →₀ N) ≃ₗ[S] ι →₀ M ⊗[R] N :=
  AlgebraTensorModule.congr (.refl S M) (finsuppLEquivDirectSum R N ι) ≪≫ₗ
    directSumRight R S M (fun _ : ι ↦ N) ≪≫ₗ (finsuppLEquivDirectSum _ _ ι).symm
/-
**TensorProduct.finsuppRight_apply_tmul** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct
`。
形式化陈述：finsuppRight_apply_tmul (m : M) (p : ι ->₀ N) : finsuppRight R S M N ι (m 
otimesₜ[R] p) = p.sum fun i n => Finsupp.single i (m otimesₜ[R] n)
参数：m : M；p : ι ->₀ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.induction_linear`：induction_linear {motive : (ι ->₀ M) -> Prop} 
(f : ι ->₀ M) (zero : motive 0) (add : forall f g : ι ->₀ M, motive f -> motive 
g -> motive (f…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Finsupp.sum_add_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : DecidableEq α] [inst_1 : AddZeroClass M]   [inst_2 : AddCommMonoid N] {f 
g : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `finsuppLEquivDirectSum_single`：finsuppLEquivDirectSum_single (i : ι) (m 
: M) : finsuppLEquivDirectSum R M ι (Finsupp.single i m) = DirectSum.lof R ι _ i
 m
· 使用定理 `TensorProduct.directSumRight_tmul_lof`：directSumRight_tmul_lof (x : M₁')
 (i : ι₂) (y : M₂ i) : directSumRight R S M₁' M₂ (x otimesₜ[R] DirectSum.lof R _
 _ i y) = DirectSum.lof S _…
· 使用定理 `finsuppLEquivDirectSum_symm_lof`：finsuppLEquivDirectSum_symm_lof (i : ι)
 (m : M) : (finsuppLEquivDirectSum R M ι).symm (DirectSum.lof R ι _ i m) = Finsu
pp.single i m
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
-/
lemma finsuppRight_apply_tmul (m : M) (p : ι →₀ N) :
    finsuppRight R S M N ι (m ⊗ₜ[R] p) = p.sum fun i n ↦ Finsupp.single i (m ⊗ₜ[R] n) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [tmul_add, map_add, hf, hg, Finsupp.sum_add_index]
  | single => simp [finsuppRight]

@[simp]
/-
**TensorProduct.finsuppRight_apply_tmul_apply** 是 Mathlib 中的一个引理，位于命名空间 `TensorP
roduct`。
形式化陈述：finsuppRight_apply_tmul_apply (m : M) (p : ι ->₀ N) (i : ι) : finsuppRight
 R S M N ι (m otimesₜ[R] p) i = m otimesₜ[R] p i
参数：m : M；p : ι ->₀ N；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.finsuppRight_apply_tmul`：finsuppRight_apply_tmul (m : M) (
p : ι ->₀ N) : finsuppRight R S M N ι (m otimesₜ[R] p) = p.sum fun i n => Finsup
p.single i (m otimesₜ[R] n)
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Finsupp.sum_eq_single`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M} (a : α)   {g : α → M → N}
, (∀ (b : α…
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
lemma finsuppRight_apply_tmul_apply (m : M) (p : ι →₀ N) (i : ι) :
    finsuppRight R S M N ι (m ⊗ₜ[R] p) i = m ⊗ₜ[R] p i := by
  rw [finsuppRight_apply_tmul, Finsupp.sum_apply,
    Finsupp.sum_eq_single i (fun _ _ ↦ Finsupp.single_eq_of_ne') (by simp), Finsupp.single_eq_same]
/-
**TensorProduct.finsuppRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：finsuppRight_apply (t : M otimes[R] (ι ->₀ N)) (i : ι) : finsuppRight R S 
M N ι t i = lTensor M (Finsupp.lapply i) t
参数：t : M otimes[R] (ι ->₀ N)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `TensorProduct.finsuppRight_apply_tmul_apply`：finsuppRight_apply_tmul_app
ly (m : M) (p : ι ->₀ N) (i : ι) : finsuppRight R S M N ι (m otimesₜ[R] p) i = m
 otimesₜ[R] p i
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem finsuppRight_apply (t : M ⊗[R] (ι →₀ N)) (i : ι) :
    finsuppRight R S M N ι t i = lTensor M (Finsupp.lapply i) t := by
  induction t with
  | zero => simp
  | tmul m f => simp [finsuppRight_apply_tmul_apply]
  | add x y hx hy => simp [map_add, hx, hy]

@[simp]
/-
**TensorProduct.finsuppRight_tmul_single** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduc
t`。
形式化陈述：finsuppRight_tmul_single (i : ι) (m : M) (n : N) : finsuppRight R S M N ι 
(m otimesₜ[R] Finsupp.single i n) = Finsupp.single i (m otimesₜ[R] n)
参数：i : ι；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.finsuppRight_apply_tmul_apply`：finsuppRight_apply_tmul_app
ly (m : M) (p : ι ->₀ N) (i : ι) : finsuppRight R S M N ι (m otimesₜ[R] p) i = m
 otimesₜ[R] p i
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
lemma finsuppRight_tmul_single (i : ι) (m : M) (n : N) :
    finsuppRight R S M N ι (m ⊗ₜ[R] Finsupp.single i n) = Finsupp.single i (m ⊗ₜ[R] n) := by
  ext; simp +contextual [Finsupp.single_apply, apply_ite]

@[simp]
/-
**TensorProduct.finsuppRight_symm_apply_single** 是 Mathlib 中的一个引理，位于命名空间 `Tensor
Product`。
形式化陈述：finsuppRight_symm_apply_single (i : ι) (m : M) (n : N) : (finsuppRight R S
 M N ι).symm (Finsupp.single i (m otimesₜ[R] n)) = m otimesₜ[R] Finsupp.single i
 n
参数：i : ι；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.finsuppRight_tmul_single`：finsuppRight_tmul_single (i : ι)
 (m : M) (n : N) : finsuppRight R S M N ι (m otimesₜ[R] Finsupp.single i n) = Fi
nsupp.single i (m otimesₜ[R]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finsuppRight_symm_apply_single (i : ι) (m : M) (n : N) :
    (finsuppRight R S M N ι).symm (Finsupp.single i (m ⊗ₜ[R] n)) =
      m ⊗ₜ[R] Finsupp.single i n := by
  simp [LinearEquiv.symm_apply_eq]

set_option backward.isDefEq.respectTransparency false in
/-
**TensorProduct.finsuppLeft_smul'** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：finsuppLeft_smul' (s : S) (t : (ι ->₀ M) otimes[R] N) : finsuppLeft R S M 
N ι (s • t) = s • finsuppLeft R S M N ι t
参数：s : S；t : (ι ->₀ M) otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finsuppLeft_smul' (s : S) (t : (ι →₀ M) ⊗[R] N) :
    finsuppLeft R S M N ι (s • t) = s • finsuppLeft R S M N ι t := by
  simp

@[deprecated (since := "2026-01-01")] alias finsuppLeft' := finsuppLeft

@[nolint synTaut, deprecated "is syntactic rfl now" (since := "2026-01-01")]
/-
**TensorProduct.finsuppLeft'_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 S] [inst_2 : Algebra R S] {M : Type u_3}   [inst_3 : AddCommMonoid M] [inst_4 :
 _root_.Module R M] [inst_5 : _root_.Module S M] [inst_6 : IsScalarTower R S M] 
  {N : Type u_4} [inst_7 : AddCommMonoid N] [inst_8 : _root_.Module R N] {ι : Ty
pe u_5} [inst_9 : DecidableEq ι]   (x : TensorProduct R (ι →₀ M) N), (TensorProd
uct.finsuppLeft R S M N ι) x = (TensorProduct.finsuppLeft R S M N ι) x
参数：x : TensorProduct R (ι →₀ M) N；TensorProduct.finsuppLeft R S M N ι；TensorProd
uct.finsuppLeft R S M N ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma finsuppLeft'_apply (x : (ι →₀ M) ⊗[R] N) :
    finsuppLeft R S M N ι x = finsuppLeft R S M N ι x := rfl

variable (R M N ι) in
/-- The tensor product of `ι →₀ R` and `N` is linearly equivalent to `ι →₀ N` -/
/-
**TensorProduct.finsuppScalarLeft** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：finsuppScalarLeft : (ι ->₀ R) otimes[R] N ≃ₗ[R] ι ->₀ N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of `ι →₀ R` and `N` is linearly equivalent to `ι →₀ N`
-/
noncomputable def finsuppScalarLeft :
    (ι →₀ R) ⊗[R] N ≃ₗ[R] ι →₀ N :=
  finsuppLeft R R R N ι ≪≫ₗ (Finsupp.mapRange.linearEquiv (TensorProduct.lid R N))

@[simp]
/-
**TensorProduct.finsuppScalarLeft_apply_tmul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Te
nsorProduct`。
形式化陈述：finsuppScalarLeft_apply_tmul_apply (p : ι ->₀ R) (n : N) (i : ι) : finsupp
ScalarLeft R N ι (p otimesₜ[R] n) i = p i • n
参数：p : ι ->₀ R；n : N；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `Finsupp.mapRange.linearEquiv_apply`：∀ {α : Type u_1} {M : Type u_2} {N :
 Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring
 R₂]   [inst_2 : AddComm…
· 使用引理 `TensorProduct.finsuppLeft_apply_tmul_apply`：finsuppLeft_apply_tmul_apply
 (p : ι ->₀ M) (n : N) (i : ι) : finsuppLeft R S M N ι (p otimesₜ[R] n) i = p i 
otimesₜ[R] n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finsuppScalarLeft_apply_tmul_apply (p : ι →₀ R) (n : N) (i : ι) :
    finsuppScalarLeft R N ι (p ⊗ₜ[R] n) i = p i • n := by
  simp [finsuppScalarLeft]
/-
**TensorProduct.finsuppScalarLeft_apply_tmul** 是 Mathlib 中的一个引理，位于命名空间 `TensorPr
oduct`。
形式化陈述：finsuppScalarLeft_apply_tmul (p : ι ->₀ R) (n : N) : finsuppScalarLeft R N
 ι (p otimesₜ[R] n) = p.sum fun i m => Finsupp.single i (m • n)
参数：p : ι ->₀ R；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.finsuppScalarLeft_apply_tmul_apply`：finsuppScalarLeft_appl
y_tmul_apply (p : ι ->₀ R) (n : N) (i : ι) : finsuppScalarLeft R N ι (p otimesₜ[
R] n) i = p i • n
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Finsupp.sum_eq_single`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M} (a : α)   {g : α → M → N}
, (∀ (b : α…
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
lemma finsuppScalarLeft_apply_tmul (p : ι →₀ R) (n : N) :
    finsuppScalarLeft R N ι (p ⊗ₜ[R] n) = p.sum fun i m ↦ Finsupp.single i (m • n) := by
  ext i
  rw [finsuppScalarLeft_apply_tmul_apply, Finsupp.sum_apply,
    Finsupp.sum_eq_single i (fun _ _ ↦ Finsupp.single_eq_of_ne') (by simp), Finsupp.single_eq_same]
/-
**TensorProduct.finsuppScalarLeft_apply** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct
`。
形式化陈述：finsuppScalarLeft_apply (pn : (ι ->₀ R) otimes[R] N) (i : ι) : finsuppScal
arLeft R N ι pn i = TensorProduct.lid R N ((Finsupp.lapply i).rTensor N pn)
参数：pn : (ι ->₀ R) otimes[R] N；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `Finsupp.mapRange.linearEquiv_apply`：∀ {α : Type u_1} {M : Type u_2} {N :
 Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring
 R₂]   [inst_2 : AddComm…
· 使用定理 `TensorProduct.finsuppLeft_apply`：finsuppLeft_apply (t : (ι ->₀ M) otimes
[R] N) (i : ι) : finsuppLeft R S M N ι t i = rTensor N (Finsupp.lapply i) t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finsuppScalarLeft_apply (pn : (ι →₀ R) ⊗[R] N) (i : ι) :
    finsuppScalarLeft R N ι pn i = TensorProduct.lid R N ((Finsupp.lapply i).rTensor N pn) := by
  simp [finsuppScalarLeft, finsuppLeft_apply]

@[simp]
/-
**TensorProduct.finsuppScalarLeft_symm_apply_single** 是 Mathlib 中的一个引理，位于命名空间 `T
ensorProduct`。
形式化陈述：finsuppScalarLeft_symm_apply_single (i : ι) (n : N) : (finsuppScalarLeft R
 N ι).symm (Finsupp.single i n) = (Finsupp.single i 1) otimesₜ[R] n
参数：i : ι；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `Finsupp.mapRange.linearEquiv_symm`：∀ {α : Type u_1} {M : Type u_2} {N : 
Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring 
R₂]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `Finsupp.mapRange.linearEquiv_apply`：∀ {α : Type u_1} {M : Type u_2} {N :
 Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring
 R₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用引理 `TensorProduct.finsuppLeft_symm_apply_single`：finsuppLeft_symm_apply_sing
le (i : ι) (m : M) (n : N) : (finsuppLeft R S M N ι).symm (Finsupp.single i (m o
timesₜ[R] n)) = Finsupp.single i …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finsuppScalarLeft_symm_apply_single (i : ι) (n : N) :
    (finsuppScalarLeft R N ι).symm (Finsupp.single i n) =
      (Finsupp.single i 1) ⊗ₜ[R] n := by
  simp [finsuppScalarLeft, finsuppLeft_symm_apply_single]

variable (R S M N ι) in
/-- The tensor product of `M` and `ι →₀ R` is linearly equivalent to `ι →₀ M` -/
/-
**TensorProduct.finsuppScalarRight** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：finsuppScalarRight : M otimes[R] (ι ->₀ R) ≃ₗ[S] ι ->₀ M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
The tensor product of `M` and `ι →₀ R` is linearly equivalent to `ι →₀ M`
-/
noncomputable def finsuppScalarRight :
    M ⊗[R] (ι →₀ R) ≃ₗ[S] ι →₀ M :=
  finsuppRight R S M R ι ≪≫ₗ Finsupp.mapRange.linearEquiv (AlgebraTensorModule.rid R S M)

@[simp]
/-
**TensorProduct.finsuppScalarRight_apply_tmul_apply** 是 Mathlib 中的一个引理，位于命名空间 `T
ensorProduct`。
形式化陈述：finsuppScalarRight_apply_tmul_apply (m : M) (p : ι ->₀ R) (i : ι) : finsup
pScalarRight R S M ι (m otimesₜ[R] p) i = p i • m
参数：m : M；p : ι ->₀ R；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `Finsupp.mapRange.linearEquiv_apply`：∀ {α : Type u_1} {M : Type u_2} {N :
 Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring
 R₂]   [inst_2 : AddComm…
· 使用引理 `TensorProduct.finsuppRight_apply_tmul_apply`：finsuppRight_apply_tmul_app
ly (m : M) (p : ι ->₀ N) (i : ι) : finsuppRight R S M N ι (m otimesₜ[R] p) i = m
 otimesₜ[R] p i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finsuppScalarRight_apply_tmul_apply (m : M) (p : ι →₀ R) (i : ι) :
    finsuppScalarRight R S M ι (m ⊗ₜ[R] p) i = p i • m := by
  simp [finsuppScalarRight]
/-
**TensorProduct.finsuppScalarRight_apply_tmul** 是 Mathlib 中的一个引理，位于命名空间 `TensorP
roduct`。
形式化陈述：finsuppScalarRight_apply_tmul (m : M) (p : ι ->₀ R) : finsuppScalarRight R
 S M ι (m otimesₜ[R] p) = p.sum fun i n => Finsupp.single i (n • m)
参数：m : M；p : ι ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.finsuppScalarRight_apply_tmul_apply`：finsuppScalarRight_ap
ply_tmul_apply (m : M) (p : ι ->₀ R) (i : ι) : finsuppScalarRight R S M ι (m oti
mesₜ[R] p) i = p i • m
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Finsupp.sum_eq_single`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M} (a : α)   {g : α → M → N}
, (∀ (b : α…
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
lemma finsuppScalarRight_apply_tmul (m : M) (p : ι →₀ R) :
    finsuppScalarRight R S M ι (m ⊗ₜ[R] p) = p.sum fun i n ↦ Finsupp.single i (n • m) := by
  ext i
  rw [finsuppScalarRight_apply_tmul_apply, Finsupp.sum_apply,
    Finsupp.sum_eq_single i (fun _ _ ↦ Finsupp.single_eq_of_ne') (by simp), Finsupp.single_eq_same]
/-
**TensorProduct.finsuppScalarRight_apply** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduc
t`。
形式化陈述：finsuppScalarRight_apply (t : M otimes[R] (ι ->₀ R)) (i : ι) : finsuppScal
arRight R S M ι t i = AlgebraTensorModule.rid R S M ((Finsupp.lapply i).lTensor 
M t)
参数：t : M otimes[R] (ι ->₀ R)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `Finsupp.mapRange.linearEquiv_apply`：∀ {α : Type u_1} {M : Type u_2} {N :
 Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring
 R₂]   [inst_2 : AddComm…
· 使用定理 `TensorProduct.finsuppRight_apply`：finsuppRight_apply (t : M otimes[R] (ι
 ->₀ N)) (i : ι) : finsuppRight R S M N ι t i = lTensor M (Finsupp.lapply i) t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finsuppScalarRight_apply (t : M ⊗[R] (ι →₀ R)) (i : ι) :
    finsuppScalarRight R S M ι t i =
      AlgebraTensorModule.rid R S M ((Finsupp.lapply i).lTensor M t) := by
  simp [finsuppScalarRight, finsuppRight_apply]

@[simp]
/-
**TensorProduct.finsuppScalarRight_symm_apply_single** 是 Mathlib 中的一个引理，位于命名空间 `
TensorProduct`。
形式化陈述：finsuppScalarRight_symm_apply_single (i : ι) (m : M) : (finsuppScalarRight
 R S M ι).symm (Finsupp.single i m) = m otimesₜ[R] (Finsupp.single i 1)
参数：i : ι；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `Finsupp.mapRange.linearEquiv_symm`：∀ {α : Type u_1} {M : Type u_2} {N : 
Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring 
R₂]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `Finsupp.mapRange.linearEquiv_apply`：∀ {α : Type u_1} {M : Type u_2} {N :
 Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring
 R₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用引理 `TensorProduct.finsuppRight_symm_apply_single`：finsuppRight_symm_apply_si
ngle (i : ι) (m : M) (n : N) : (finsuppRight R S M N ι).symm (Finsupp.single i (
m otimesₜ[R] n)) = m otimesₜ[R] Fi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finsuppScalarRight_symm_apply_single (i : ι) (m : M) :
    (finsuppScalarRight R S M ι).symm (Finsupp.single i m) =
      m ⊗ₜ[R] (Finsupp.single i 1) := by
  simp [finsuppScalarRight, finsuppRight_symm_apply_single]

set_option backward.isDefEq.respectTransparency false in
/-
**TensorProduct.finsuppScalarRight_smul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct
`。
形式化陈述：finsuppScalarRight_smul (s : S) (t) : finsuppScalarRight R S M ι (s • t) =
 s • finsuppScalarRight R S M ι t
参数：s : S；t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsuppScalarRight_smul (s : S) (t) :
    finsuppScalarRight R S M ι (s • t) = s • finsuppScalarRight R S M ι t := by
  simp

@[deprecated (since := "2026-01-01")] alias finsuppScalarRight' := finsuppScalarRight

@[nolint synTaut, deprecated "is syntactic rfl now" (since := "2026-01-01")]
/-
**TensorProduct.coe_finsuppScalarRight'** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct
`。
形式化陈述：coe_finsuppScalarRight' : ⇑(finsuppScalarRight R S M ι) = finsuppScalarRig
ht R S M ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem coe_finsuppScalarRight' :
    ⇑(finsuppScalarRight R S M ι) = finsuppScalarRight R S M ι :=
  rfl

end TensorProduct

end TensorProduct

variable (R S M N ι κ : Type*)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [Semiring S] [Algebra R S]

/-
**Finsupp.linearCombination_one_tmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.linearCombination_one_tmul [DecidableEq ι] {v : ι -> M} : (linearC
ombination S ((1 : S) otimesₜ[R] v ·)).restrictScalars R = (linearCombination R 
v).lTensor S ∘ₗ (finsuppScalarRight R R S ι).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.CompatibleSMul.finsupp_dom`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `TensorProduct.finsuppScalarRight_symm_apply_single`：finsuppScalarRight_s
ymm_apply_single (i : ι) (m : M) : (finsuppScalarRight R S M ι).symm (Finsupp.si
ngle i m) = m otimesₜ[R] (Finsupp.single…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finsupp.linearCombination_one_tmul [DecidableEq ι] {v : ι → M} :
    (linearCombination S ((1 : S) ⊗ₜ[R] v ·)).restrictScalars R =
      (linearCombination R v).lTensor S ∘ₗ (finsuppScalarRight R R S ι).symm := by
  ext; simp [smul_tmul']

variable [Module S M] [IsScalarTower R S M]

open scoped Classical in
/-- The tensor product of `ι →₀ M` and `κ →₀ N` is linearly equivalent to `(ι × κ) →₀ (M ⊗ N)`. -/
/-
**finsuppTensorFinsupp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finsuppTensorFinsupp : (ι ->₀ M) otimes[R] (κ ->₀ N) ≃ₗ[S] ι × κ ->₀ M oti
mes[R] N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
The tensor product of `ι →₀ M` and `κ →₀ N` is linearly equivalent to `(ι × κ) →
₀ (M ⊗ N)`.
-/
def finsuppTensorFinsupp : (ι →₀ M) ⊗[R] (κ →₀ N) ≃ₗ[S] ι × κ →₀ M ⊗[R] N :=
  TensorProduct.AlgebraTensorModule.congr
    (finsuppLEquivDirectSum S M ι) (finsuppLEquivDirectSum R N κ) ≪≫ₗ
    ((TensorProduct.directSum R S (fun _ : ι => M) fun _ : κ => N) ≪≫ₗ
      (finsuppLEquivDirectSum S (M ⊗[R] N) (ι × κ)).symm)

@[simp]
/-
**finsuppTensorFinsupp_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppTensorFinsupp_single (i : ι) (m : M) (k : κ) (n : N) : finsuppTenso
rFinsupp R S M N ι κ (Finsupp.single i m otimesₜ Finsupp.single k n) = Finsupp.s
ingle (i, k) (m otimesₜ n)
参数：i : ι；m : M；k : κ；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `finsuppLEquivDirectSum_single`：finsuppLEquivDirectSum_single (i : ι) (m 
: M) : finsuppLEquivDirectSum R M ι (Finsupp.single i m) = DirectSum.lof R ι _ i
 m
· 使用定理 `TensorProduct.directSum_lof_tmul_lof`：directSum_lof_tmul_lof (i₁ : ι₁) (
m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) : TensorProduct.directSum R S M₁ M₂ (DirectSu
m.lof S ι₁ M₁ i₁ m₁ otimes…
· 使用定理 `finsuppLEquivDirectSum_symm_lof`：finsuppLEquivDirectSum_symm_lof (i : ι)
 (m : M) : (finsuppLEquivDirectSum R M ι).symm (DirectSum.lof R ι _ i m) = Finsu
pp.single i m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsuppTensorFinsupp_single (i : ι) (m : M) (k : κ) (n : N) :
    finsuppTensorFinsupp R S M N ι κ (Finsupp.single i m ⊗ₜ Finsupp.single k n) =
      Finsupp.single (i, k) (m ⊗ₜ n) := by
  simp [finsuppTensorFinsupp]

@[simp]
/-
**finsuppTensorFinsupp_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppTensorFinsupp_apply (f : ι ->₀ M) (g : κ ->₀ N) (i : ι) (k : κ) : f
insuppTensorFinsupp R S M N ι κ (f otimesₜ g) (i, k) = f i otimesₜ g k
参数：f : ι ->₀ M；g : κ ->₀ N；i : ι；k : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.induction_linear`：induction_linear {motive : (ι ->₀ M) -> Prop} 
(f : ι ->₀ M) (zero : motive 0) (add : forall f g : ι ->₀ M, motive f -> motive 
g -> motive (f…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `finsuppTensorFinsupp_single`：finsuppTensorFinsupp_single (i : ι) (m : M)
 (k : κ) (n : N) : finsuppTensorFinsupp R S M N ι κ (Finsupp.single i m otimesₜ 
Finsupp.single k …
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_and`：ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem finsuppTensorFinsupp_apply (f : ι →₀ M) (g : κ →₀ N) (i : ι) (k : κ) :
    finsuppTensorFinsupp R S M N ι κ (f ⊗ₜ g) (i, k) = f i ⊗ₜ g k := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ hf₁ hf₂ => simp [add_tmul, hf₁, hf₂]
  | single i' m =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ hg₁ hg₂ => simp [tmul_add, hg₁, hg₂]
    | single k' n =>
      classical
      simp_rw [finsuppTensorFinsupp_single, Finsupp.single_apply, Prod.mk_inj, ite_and]
      split_ifs <;> simp

@[simp]
/-
**finsuppTensorFinsupp_symm_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppTensorFinsupp_symm_single (i : ι × κ) (m : M) (n : N) : (finsuppTen
sorFinsupp R S M N ι κ).symm (Finsupp.single i (m otimesₜ n)) = Finsupp.single i
.1 m otimesₜ Finsupp.single i.2 n
参数：i : ι × κ；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finsuppTensorFinsupp_single`：finsuppTensorFinsupp_single (i : ι) (m : M)
 (k : κ) (n : N) : finsuppTensorFinsupp R S M N ι κ (Finsupp.single i m otimesₜ 
Finsupp.single k …
-/
theorem finsuppTensorFinsupp_symm_single (i : ι × κ) (m : M) (n : N) :
    (finsuppTensorFinsupp R S M N ι κ).symm (Finsupp.single i (m ⊗ₜ n)) =
      Finsupp.single i.1 m ⊗ₜ Finsupp.single i.2 n :=
  Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsupp_single _ _ _ _ _ _ _ _ _ _).symm

/-- A variant of `finsuppTensorFinsupp` where the first module is the ground ring. -/
/-
**finsuppTensorFinsuppLid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finsuppTensorFinsuppLid : (ι ->₀ R) otimes[R] (κ ->₀ N) ≃ₗ[R] ι × κ ->₀ N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
A variant of `finsuppTensorFinsupp` where the first module is the ground ring.
-/
def finsuppTensorFinsuppLid : (ι →₀ R) ⊗[R] (κ →₀ N) ≃ₗ[R] ι × κ →₀ N :=
  finsuppTensorFinsupp R R R N ι κ ≪≫ₗ Finsupp.lcongr (Equiv.refl _) (TensorProduct.lid R N)

@[simp]
/-
**finsuppTensorFinsuppLid_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppTensorFinsuppLid_apply_apply (f : ι ->₀ R) (g : κ ->₀ N) (a : ι) (b
 : κ) : finsuppTensorFinsuppLid R N ι κ (f otimesₜ[R] g) (a, b) = f a • g b
参数：f : ι ->₀ R；g : κ ->₀ N；a : ι；b : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `finsuppTensorFinsupp_apply`：finsuppTensorFinsupp_apply (f : ι ->₀ M) (g 
: κ ->₀ N) (i : ι) (k : κ) : finsuppTensorFinsupp R S M N ι κ (f otimesₜ g) (i, 
k) = f i otimesₜ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsuppTensorFinsuppLid_apply_apply (f : ι →₀ R) (g : κ →₀ N) (a : ι) (b : κ) :
    finsuppTensorFinsuppLid R N ι κ (f ⊗ₜ[R] g) (a, b) = f a • g b := by
  simp [finsuppTensorFinsuppLid]

@[simp]
/-
**finsuppTensorFinsuppLid_single_tmul_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppTensorFinsuppLid_single_tmul_single (a : ι) (b : κ) (r : R) (n : N)
 : finsuppTensorFinsuppLid R N ι κ (Finsupp.single a r otimesₜ[R] Finsupp.single
 b n) = Finsupp.single (a, b) (r • n)
参数：a : ι；b : κ；r : R；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `finsuppTensorFinsupp_single`：finsuppTensorFinsupp_single (i : ι) (m : M)
 (k : κ) (n : N) : finsuppTensorFinsupp R S M N ι κ (Finsupp.single i m otimesₜ 
Finsupp.single k …
· 使用定理 `Finsupp.lcongr_single`：lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M
 ≃ₛₗ[σ] N) (i : ι) (m : M) : lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single 
(e₁ i) (e₂ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsuppTensorFinsuppLid_single_tmul_single (a : ι) (b : κ) (r : R) (n : N) :
    finsuppTensorFinsuppLid R N ι κ (Finsupp.single a r ⊗ₜ[R] Finsupp.single b n) =
      Finsupp.single (a, b) (r • n) := by
  simp [finsuppTensorFinsuppLid]

@[simp]
/-
**finsuppTensorFinsuppLid_symm_single_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppTensorFinsuppLid_symm_single_smul (i : ι × κ) (r : R) (n : N) : (fi
nsuppTensorFinsuppLid R N ι κ).symm (Finsupp.single i (r • n)) = Finsupp.single 
i.1 r otimesₜ Finsupp.single i.2 n
参数：i : ι × κ；r : R；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finsuppTensorFinsuppLid_single_tmul_single`：finsuppTensorFinsuppLid_sing
le_tmul_single (a : ι) (b : κ) (r : R) (n : N) : finsuppTensorFinsuppLid R N ι κ
 (Finsupp.single a r otimesₜ[R] …
-/
theorem finsuppTensorFinsuppLid_symm_single_smul (i : ι × κ) (r : R) (n : N) :
    (finsuppTensorFinsuppLid R N ι κ).symm (Finsupp.single i (r • n)) =
      Finsupp.single i.1 r ⊗ₜ Finsupp.single i.2 n :=
  Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsuppLid_single_tmul_single ..).symm

/-- A variant of `finsuppTensorFinsupp` where the second module is the ground ring. -/
/-
**finsuppTensorFinsuppRid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finsuppTensorFinsuppRid : (ι ->₀ M) otimes[R] (κ ->₀ R) ≃ₗ[R] ι × κ ->₀ M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
A variant of `finsuppTensorFinsupp` where the second module is the ground ring.
-/
def finsuppTensorFinsuppRid : (ι →₀ M) ⊗[R] (κ →₀ R) ≃ₗ[R] ι × κ →₀ M :=
  finsuppTensorFinsupp R R M R ι κ ≪≫ₗ Finsupp.lcongr (Equiv.refl _) (TensorProduct.rid R M)

@[simp]
/-
**finsuppTensorFinsuppRid_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppTensorFinsuppRid_apply_apply (f : ι ->₀ M) (g : κ ->₀ R) (a : ι) (b
 : κ) : finsuppTensorFinsuppRid R M ι κ (f otimesₜ[R] g) (a, b) = g b • f a
参数：f : ι ->₀ M；g : κ ->₀ R；a : ι；b : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `finsuppTensorFinsupp_apply`：finsuppTensorFinsupp_apply (f : ι ->₀ M) (g 
: κ ->₀ N) (i : ι) (k : κ) : finsuppTensorFinsupp R S M N ι κ (f otimesₜ g) (i, 
k) = f i otimesₜ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsuppTensorFinsuppRid_apply_apply (f : ι →₀ M) (g : κ →₀ R) (a : ι) (b : κ) :
    finsuppTensorFinsuppRid R M ι κ (f ⊗ₜ[R] g) (a, b) = g b • f a := by
  simp [finsuppTensorFinsuppRid]

@[simp]
/-
**finsuppTensorFinsuppRid_single_tmul_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppTensorFinsuppRid_single_tmul_single (a : ι) (b : κ) (m : M) (r : R)
 : finsuppTensorFinsuppRid R M ι κ (Finsupp.single a m otimesₜ[R] Finsupp.single
 b r) = Finsupp.single (a, b) (r • m)
参数：a : ι；b : κ；m : M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `finsuppTensorFinsupp_single`：finsuppTensorFinsupp_single (i : ι) (m : M)
 (k : κ) (n : N) : finsuppTensorFinsupp R S M N ι κ (Finsupp.single i m otimesₜ 
Finsupp.single k …
· 使用定理 `Finsupp.lcongr_single`：lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M
 ≃ₛₗ[σ] N) (i : ι) (m : M) : lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single 
(e₁ i) (e₂ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finsuppTensorFinsuppRid_single_tmul_single (a : ι) (b : κ) (m : M) (r : R) :
    finsuppTensorFinsuppRid R M ι κ (Finsupp.single a m ⊗ₜ[R] Finsupp.single b r) =
      Finsupp.single (a, b) (r • m) := by
  simp [finsuppTensorFinsuppRid]

@[simp]
/-
**finsuppTensorFinsuppRid_symm_single_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppTensorFinsuppRid_symm_single_smul (i : ι × κ) (m : M) (r : R) : (fi
nsuppTensorFinsuppRid R M ι κ).symm (Finsupp.single i (r • m)) = Finsupp.single 
i.1 m otimesₜ Finsupp.single i.2 r
参数：i : ι × κ；m : M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finsuppTensorFinsuppRid_single_tmul_single`：finsuppTensorFinsuppRid_sing
le_tmul_single (a : ι) (b : κ) (m : M) (r : R) : finsuppTensorFinsuppRid R M ι κ
 (Finsupp.single a m otimesₜ[R] …
-/
theorem finsuppTensorFinsuppRid_symm_single_smul (i : ι × κ) (m : M) (r : R) :
    (finsuppTensorFinsuppRid R M ι κ).symm (Finsupp.single i (r • m)) =
      Finsupp.single i.1 m ⊗ₜ Finsupp.single i.2 r :=
  Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsuppRid_single_tmul_single ..).symm

/-- A variant of `finsuppTensorFinsupp` where both modules are the ground ring. -/
/-
**finsuppTensorFinsupp'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finsuppTensorFinsupp' : (ι ->₀ R) otimes[R] (κ ->₀ R) ≃ₗ[R] ι × κ ->₀ R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `finsuppTensorFinsupp` where both modules are the ground ring.
-/
def finsuppTensorFinsupp' : (ι →₀ R) ⊗[R] (κ →₀ R) ≃ₗ[R] ι × κ →₀ R :=
  finsuppTensorFinsuppLid R R ι κ

@[simp]
/-
**finsuppTensorFinsupp'_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (R : Type u_1) (ι : Type u_5) (κ : Type u_6) [inst : CommSemiring R] (f 
: ι →₀ R) (g : κ →₀ R) (a : ι) (b : κ),   ((finsuppTensorFinsupp' R ι κ) (f ⊗ₜ[R
] g)) (a, b) = f a * g b
参数：R : Type u_1；ι : Type u_5；κ : Type u_6；f : ι →₀ R；g : κ →₀ R；a : ι；b : κ；(fin
suppTensorFinsupp' R ι κ) (f ⊗ₜ[R] g)；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finsuppTensorFinsuppLid_apply_apply`：finsuppTensorFinsuppLid_apply_apply
 (f : ι ->₀ R) (g : κ ->₀ N) (a : ι) (b : κ) : finsuppTensorFinsuppLid R N ι κ (
f otimesₜ[R] g) (a, b) = …
-/
theorem finsuppTensorFinsupp'_apply_apply (f : ι →₀ R) (g : κ →₀ R) (a : ι) (b : κ) :
    finsuppTensorFinsupp' R ι κ (f ⊗ₜ[R] g) (a, b) = f a * g b :=
  finsuppTensorFinsuppLid_apply_apply R R ι κ f g a b

@[simp]
/-
**finsuppTensorFinsupp'_single_tmul_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (R : Type u_1) (ι : Type u_5) (κ : Type u_6) [inst : CommSemiring R] (a 
: ι) (b : κ) (r₁ r₂ : R),   (finsuppTensorFinsupp' R ι κ) ((fun₀ | a => r₁) ⊗ₜ[R
] fun₀ | b => r₂) = fun₀ | (a, b) => r₁ * r₂
参数：R : Type u_1；ι : Type u_5；κ : Type u_6；a : ι；b : κ；r₁ r₂ : R；finsuppTensorFin
supp' R ι κ；(fun₀ | a => r₁) ⊗ₜ[R] fun₀ | b => r₂；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finsuppTensorFinsuppLid_single_tmul_single`：finsuppTensorFinsuppLid_sing
le_tmul_single (a : ι) (b : κ) (r : R) (n : N) : finsuppTensorFinsuppLid R N ι κ
 (Finsupp.single a r otimesₜ[R] …
-/
theorem finsuppTensorFinsupp'_single_tmul_single (a : ι) (b : κ) (r₁ r₂ : R) :
    finsuppTensorFinsupp' R ι κ (Finsupp.single a r₁ ⊗ₜ[R] Finsupp.single b r₂) =
      Finsupp.single (a, b) (r₁ * r₂) :=
  finsuppTensorFinsuppLid_single_tmul_single R R ι κ a b r₁ r₂
/-
**finsuppTensorFinsupp'_symm_single_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (R : Type u_1) (ι : Type u_5) (κ : Type u_6) [inst : CommSemiring R] (i 
: ι × κ) (r₁ r₂ : R),   ((finsuppTensorFinsupp' R ι κ).symm fun₀ | i => r₁ * r₂)
 = (fun₀ | i.1 => r₁) ⊗ₜ[R] fun₀ | i.2 => r₂
参数：R : Type u_1；ι : Type u_5；κ : Type u_6；i : ι × κ；r₁ r₂ : R；(finsuppTensorFins
upp' R ι κ).symm fun₀ | i => r₁ * r₂；fun₀ | i.1 => r₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finsuppTensorFinsuppLid_symm_single_smul`：finsuppTensorFinsuppLid_symm_s
ingle_smul (i : ι × κ) (r : R) (n : N) : (finsuppTensorFinsuppLid R N ι κ).symm 
(Finsupp.single i (r • n)) = F…
-/
theorem finsuppTensorFinsupp'_symm_single_mul (i : ι × κ) (r₁ r₂ : R) :
    (finsuppTensorFinsupp' R ι κ).symm (Finsupp.single i (r₁ * r₂)) =
      Finsupp.single i.1 r₁ ⊗ₜ Finsupp.single i.2 r₂ :=
  finsuppTensorFinsuppLid_symm_single_smul R R ι κ i r₁ r₂
/-
**finsuppTensorFinsupp'_symm_single_eq_single_one_tmul** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：∀ (R : Type u_1) (ι : Type u_5) (κ : Type u_6) [inst : CommSemiring R] (i 
: ι × κ) (r : R),   ((finsuppTensorFinsupp' R ι κ).symm fun₀ | i => r) = (fun₀ |
 i.1 => 1) ⊗ₜ[R] fun₀ | i.2 => r
参数：R : Type u_1；ι : Type u_5；κ : Type u_6；i : ι × κ；r : R；(finsuppTensorFinsupp'
 R ι κ).symm fun₀ | i => r；fun₀ | i.1 => 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `finsuppTensorFinsupp'_symm_single_mul`：∀ (R : Type u_1) (ι : Type u_5) (
κ : Type u_6) [inst : CommSemiring R] (i : ι × κ) (r₁ r₂ : R),   ((finsuppTensor
Finsupp' R ι κ).symm fun₀ |…
-/
theorem finsuppTensorFinsupp'_symm_single_eq_single_one_tmul (i : ι × κ) (r : R) :
    (finsuppTensorFinsupp' R ι κ).symm (Finsupp.single i r) =
      Finsupp.single i.1 1 ⊗ₜ Finsupp.single i.2 r := by
  nth_rw 1 [← one_mul r]
  exact finsuppTensorFinsupp'_symm_single_mul R ι κ i _ _
/-
**finsuppTensorFinsupp'_symm_single_eq_tmul_single_one** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：∀ (R : Type u_1) (ι : Type u_5) (κ : Type u_6) [inst : CommSemiring R] (i 
: ι × κ) (r : R),   ((finsuppTensorFinsupp' R ι κ).symm fun₀ | i => r) = (fun₀ |
 i.1 => r) ⊗ₜ[R] fun₀ | i.2 => 1
参数：R : Type u_1；ι : Type u_5；κ : Type u_6；i : ι × κ；r : R；(finsuppTensorFinsupp'
 R ι κ).symm fun₀ | i => r；fun₀ | i.1 => r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `finsuppTensorFinsupp'_symm_single_mul`：∀ (R : Type u_1) (ι : Type u_5) (
κ : Type u_6) [inst : CommSemiring R] (i : ι × κ) (r₁ r₂ : R),   ((finsuppTensor
Finsupp' R ι κ).symm fun₀ |…
-/
theorem finsuppTensorFinsupp'_symm_single_eq_tmul_single_one (i : ι × κ) (r : R) :
    (finsuppTensorFinsupp' R ι κ).symm (Finsupp.single i r) =
      Finsupp.single i.1 r ⊗ₜ Finsupp.single i.2 1 := by
  nth_rw 1 [← mul_one r]
  exact finsuppTensorFinsupp'_symm_single_mul R ι κ i _ _
/-
**finsuppTensorFinsuppLid_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppTensorFinsuppLid_self : finsuppTensorFinsuppLid R R ι κ = finsuppTe
nsorFinsupp' R ι κ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finsuppTensorFinsuppLid_self :
    finsuppTensorFinsuppLid R R ι κ = finsuppTensorFinsupp' R ι κ := rfl
/-
**finsuppTensorFinsuppRid_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppTensorFinsuppRid_self : finsuppTensorFinsuppRid R R ι κ = finsuppTe
nsorFinsupp' R ι κ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsuppTensorFinsupp'.eq_1`：∀ (R : Type u_1) (ι : Type u_5) (κ : Type u_
6) [inst : CommSemiring R],   finsuppTensorFinsupp' R ι κ = finsuppTensorFinsupp
Lid R R ι κ
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `finsuppTensorFinsuppLid.eq_1`：∀ (R : Type u_1) (N : Type u_4) (ι : Type 
u_5) (κ : Type u_6) [inst : CommSemiring R] [inst_1 : AddCommMonoid N]   [inst_2
 : _root_.Module R…
· 使用定理 `finsuppTensorFinsuppRid.eq_1`：∀ (R : Type u_1) (M : Type u_3) (ι : Type 
u_5) (κ : Type u_6) [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2
 : _root_.Module R…
· 使用定理 `TensorProduct.lid_eq_rid`：lid_eq_rid : TensorProduct.lid R R = TensorPro
duct.rid R R
-/
theorem finsuppTensorFinsuppRid_self :
    finsuppTensorFinsuppRid R R ι κ = finsuppTensorFinsupp' R ι κ := by
  rw [finsuppTensorFinsupp', finsuppTensorFinsuppLid, finsuppTensorFinsuppRid,
    TensorProduct.lid_eq_rid]

end

