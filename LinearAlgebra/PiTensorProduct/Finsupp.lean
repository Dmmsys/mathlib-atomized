/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.Data.Finsupp.ToDFinsupp
public import Mathlib.LinearAlgebra.PiTensorProduct.DFinsupp
public import Mathlib.RingTheory.PiTensorProduct

/-!
# Results on finitely supported functions.

* `ofFinsuppEquiv`, the tensor product of the family `κ i →₀ M i` indexed by `ι` is linearly
  equivalent to `∏ i, κ i →₀ ⨂[R] i, M i`.
-/

@[expose] public section

namespace PiTensorProduct

open PiTensorProduct TensorProduct

attribute [local ext] TensorProduct.ext

variable {R ι : Type*} {κ M : ι → Type*}
variable [CommSemiring R] [Fintype ι] [DecidableEq ι] [(i : ι) → DecidableEq (κ i)]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, DecidableEq (M i)]

/-- If `ι` is a `Fintype`, `κ i` is a family of types indexed by `ι` and `M i` is a family
of modules indexed by `ι`, then the tensor product of the family `κ i →₀ M i` is linearly
equivalent to `∏ i, κ i →₀ ⨂[R] i, M i`.
-/
/-
**PiTensorProduct.ofFinsuppEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：ofFinsuppEquiv : (⨂[R] i, κ i ->₀ M i) ≃ₗ[R] ((i : ι) -> κ i) ->₀ ⨂[R] i, 
M i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ι` is a `Fintype`, `κ i` is a family of types indexed by `ι` and `M i` is a 
family
of modules indexed by `ι`, then the tensor product of the family `κ i →₀ M i` is
 linearly
equivalent to `∏ i, κ i →₀ ⨂[R] i, M i`.
-/
noncomputable def ofFinsuppEquiv :
    (⨂[R] i, κ i →₀ M i) ≃ₗ[R] ((i : ι) → κ i) →₀ ⨂[R] i, M i :=
  haveI := Classical.typeDecidableEq (⨂[R] (i : ι), M i)
  PiTensorProduct.congr (fun _ ↦ finsuppLequivDFinsupp R) ≪≫ₗ
    ofDFinsuppEquiv ≪≫ₗ
    (finsuppLequivDFinsupp R).symm

@[simp]
/-
**PiTensorProduct.ofFinsuppEquiv_tprod_single** 是 Mathlib 中的一个定理，位于命名空间 `PiTenso
rProduct`。
形式化陈述：ofFinsuppEquiv_tprod_single (p : (i : ι) -> κ i) (m : (i : ι) -> M i) : of
FinsuppEquiv (⨂ₜ[R] i, Finsupp.single (p i) (m i)) = Finsupp.single p (⨂ₜ[R] i, 
m i)
参数：p : (i : ι) -> κ i；m : (i : ι) -> M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.congr_tprod`：congr_tprod (f : Π i, s i ≃ₗ[R] t i) (m : Π
 i, s i) : congr f (tprod R m) = tprod R (fun (i : ι) => (f i) (m i))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.toDFinsupp_single`：Finsupp.toDFinsupp_single (i : ι) (m : M) : (
Finsupp.single i m).toDFinsupp = DFinsupp.single i m
· 使用定理 `PiTensorProduct.ofDFinsuppEquiv_tprod_single`：ofDFinsuppEquiv_tprod_sing
le (p : Π i, κ i) (x : Π i, M i (p i)) : ofDFinsuppEquiv (⨂ₜ[R] i, DFinsupp.sing
le (p i) (x i)) = DFinsupp.single …
· 使用定理 `DFinsupp.toFinsupp_single`：DFinsupp.toFinsupp_single (i : ι) (m : M) : (
DFinsupp.single i m : Π₀ _ : ι, M).toFinsupp = Finsupp.single i m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFinsuppEquiv_tprod_single (p : (i : ι) → κ i) (m : (i : ι) → M i) :
    ofFinsuppEquiv (⨂ₜ[R] i, Finsupp.single (p i) (m i)) =
    Finsupp.single p (⨂ₜ[R] i, m i) := by
  simp [ofFinsuppEquiv]

@[simp]
/-
**PiTensorProduct.ofFinsuppEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduc
t`。
形式化陈述：ofFinsuppEquiv_apply (f : (i : ι) -> (κ i ->₀ M i)) (p : (i : ι) -> κ i) :
 ofFinsuppEquiv (⨂ₜ[R] i, f i) p = ⨂ₜ[R] i, f i (p i)
参数：f : (i : ι) -> (κ i ->₀ M i)；p : (i : ι) -> κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.congr_tprod`：congr_tprod (f : Π i, s i ≃ₗ[R] t i) (m : Π
 i, s i) : congr f (tprod R m) = tprod R (fun (i : ι) => (f i) (m i))
· 使用定理 `PiTensorProduct.ofDFinsuppEquiv_tprod_apply`：ofDFinsuppEquiv_tprod_apply
 (x : Π i, Π₀ j, M i j) (p : Π i, κ i) : ofDFinsuppEquiv (tprod R x) p = ⨂ₜ[R] i
, x i (p i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFinsuppEquiv_apply (f : (i : ι) → (κ i →₀ M i)) (p : (i : ι) → κ i) :
    ofFinsuppEquiv (⨂ₜ[R] i, f i) p = ⨂ₜ[R] i, f i (p i) := by
  simp [ofFinsuppEquiv]

@[simp]
/-
**PiTensorProduct.ofFinsuppEquiv_symm_single_tprod** 是 Mathlib 中的一个定理，位于命名空间 `Pi
TensorProduct`。
形式化陈述：ofFinsuppEquiv_symm_single_tprod (p : (i : ι) -> κ i) (m : (i : ι) -> M i)
 : ofFinsuppEquiv.symm (Finsupp.single p (⨂ₜ[R] i, m i)) = ⨂ₜ[R] i, Finsupp.sing
le (p i) (m i)
参数：p : (i : ι) -> κ i；m : (i : ι) -> M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PiTensorProduct.ofFinsuppEquiv_tprod_single`：ofFinsuppEquiv_tprod_single
 (p : (i : ι) -> κ i) (m : (i : ι) -> M i) : ofFinsuppEquiv (⨂ₜ[R] i, Finsupp.si
ngle (p i) (m i)) = Finsupp.singl…
-/
theorem ofFinsuppEquiv_symm_single_tprod (p : (i : ι) → κ i) (m : (i : ι) → M i) :
    ofFinsuppEquiv.symm (Finsupp.single p (⨂ₜ[R] i, m i)) =
    ⨂ₜ[R] i, Finsupp.single (p i) (m i) :=
  (LinearEquiv.symm_apply_eq _).2 (ofFinsuppEquiv_tprod_single _ _).symm

variable [DecidableEq R]

/-- A variant of `ofFinsuppEquiv` where all modules `M i` are the ground ring. -/
/-
**PiTensorProduct.ofFinsuppEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：ofFinsuppEquiv' : (⨂[R] i, (κ i ->₀ R)) ≃ₗ[R] ((i : ι) -> κ i) ->₀ R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
A variant of `ofFinsuppEquiv` where all modules `M i` are the ground ring.
-/
noncomputable def ofFinsuppEquiv' : (⨂[R] i, (κ i →₀ R)) ≃ₗ[R] ((i : ι) → κ i) →₀ R :=
  ofFinsuppEquiv ≪≫ₗ
  Finsupp.lcongr (Equiv.refl ((i : ι) → κ i)) (constantBaseRingEquiv ι R).toLinearEquiv

@[simp]
/-
**PiTensorProduct.ofFinsuppEquiv'_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiTenso
rProduct`。
形式化陈述：∀ {R : Type u_1} {ι : Type u_2} {κ : ι → Type u_3} [inst : CommSemiring R]
 [inst_1 : Fintype ι] [inst_2 : DecidableEq ι]   [inst_3 : (i : ι) → DecidableEq
 (κ i)] [inst_4 : DecidableEq R] (f : (i : ι) → κ i →₀ R) (p : (i : ι) → κ i),  
 (PiTensorProduct.ofFinsuppEquiv' ((PiTensorProduct.tprod R) fun i => f i)) p = 
∏ i, (f i) (p i)
参数：i : ι；κ i；f : (i : ι) → κ i →₀ R；p : (i : ι) → κ i；PiTensorProduct.ofFinsuppE
quiv' ((PiTensorProduct.tprod R) fun i => f i)；f i；p i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `PiTensorProduct.ofFinsuppEquiv_apply`：ofFinsuppEquiv_apply (f : (i : ι) 
-> (κ i ->₀ M i)) (p : (i : ι) -> κ i) : ofFinsuppEquiv (⨂ₜ[R] i, f i) p = ⨂ₜ[R]
 i, f i (p i)
· 使用定理 `AlgEquiv.toLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `PiTensorProduct.constantBaseRingEquiv_tprod`：constantBaseRingEquiv_tprod
 (x : ι -> R) : constantBaseRingEquiv ι R (tprod R x) = ∏ i, x i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFinsuppEquiv'_apply_apply (f : (i : ι) → κ i →₀ R) (p : (i : ι) → κ i) :
    ofFinsuppEquiv' (⨂ₜ[R] i, f i) p = ∏ i, f i (p i) := by
  simp [ofFinsuppEquiv']

@[simp]
/-
**PiTensorProduct.ofFinsuppEquiv'_tprod_single** 是 Mathlib 中的一个定理，位于命名空间 `PiTens
orProduct`。
形式化陈述：∀ {R : Type u_1} {ι : Type u_2} {κ : ι → Type u_3} [inst : CommSemiring R]
 [inst_1 : Fintype ι] [inst_2 : DecidableEq ι]   [inst_3 : (i : ι) → DecidableEq
 (κ i)] [inst_4 : DecidableEq R] (p : (i : ι) → κ i) (r : ι → R),   PiTensorProd
uct.ofFinsuppEquiv' ((PiTensorProduct.tprod R) fun i => fun₀ | p i => r i) = fun
₀ | p => ∏ i, r i
参数：i : ι；κ i；p : (i : ι) → κ i；r : ι → R；(PiTensorProduct.tprod R) fun i => fun₀
 | p i => r i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `PiTensorProduct.ofFinsuppEquiv_tprod_single`：ofFinsuppEquiv_tprod_single
 (p : (i : ι) -> κ i) (m : (i : ι) -> M i) : ofFinsuppEquiv (⨂ₜ[R] i, Finsupp.si
ngle (p i) (m i)) = Finsupp.singl…
· 使用定理 `Finsupp.lcongr_single`：lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M
 ≃ₛₗ[σ] N) (i : ι) (m : M) : lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single 
(e₁ i) (e₂ …
· 使用定理 `AlgEquiv.toLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `PiTensorProduct.constantBaseRingEquiv_tprod`：constantBaseRingEquiv_tprod
 (x : ι -> R) : constantBaseRingEquiv ι R (tprod R x) = ∏ i, x i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFinsuppEquiv'_tprod_single (p : (i : ι) → κ i) (r : ι → R) :
    ofFinsuppEquiv' (⨂ₜ[R] i, Finsupp.single (p i) (r i)) =
    Finsupp.single p (∏ i, r i) := by
  simp [ofFinsuppEquiv']

end PiTensorProduct

