/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison, Sophie Morel
-/
module

public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.PiTensorProduct.Finsupp

/-!
# Basis for `PiTensorProduct`

This file constructs a basis for `PiTensorProduct` given bases on the component spaces.
-/

@[expose] public section

section PiTensorProduct

attribute [local ext] PiTensorProduct.ext

open LinearMap PiTensorProduct Module TensorProduct

variable {ι R : Type*} {M : ι → Type*} {κ : ι → Type*} [CommSemiring R] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)]

open scoped Classical in
/-- Let `ι` be a `Finite` type and `M` be a family of modules indexed by `ι`. If `b i : κ i → M i`
is a basis for every `i` in `ι`, then `fun (p : Π i, κ i) ↦ ⨂ₜ[R] i, b i (p i)` is a basis
of `⨂[R] i, M i`.
-/
/-
**Basis.piTensorProduct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Basis.piTensorProduct [Finite ι] (b : Π i, Basis (κ i) R (M i)) : Basis (Π
 i, κ i) R (⨂[R] i, M i)
参数：b : Π i, Basis (κ i) R (M i)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Let `ι` be a `Finite` type and `M` be a family of modules indexed by `ι`. If `b 
i : κ i → M i`
is a basis for every `i` in `ι`, then `fun (p : Π i, κ i) ↦ ⨂ₜ[R] i, b i (p i)` 
is a basis
of `⨂[R] i, M i`.
-/
noncomputable def Basis.piTensorProduct [Finite ι] (b : Π i, Basis (κ i) R (M i)) :
    Basis (Π i, κ i) R (⨂[R] i, M i) :=
  haveI := Fintype.ofFinite ι
  Finsupp.basisSingleOne.map
    ((PiTensorProduct.congr (fun i ↦ (b i).repr)) ≪≫ₗ
      ofFinsuppEquiv ≪≫ₗ
      Finsupp.lcongr (Equiv.refl _) (constantBaseRingEquiv _ R).toLinearEquiv).symm

@[simp]
/-
**Basis.piTensorProduct_repr_tprod_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Basis.piTensorProduct_repr_tprod_apply [Fintype ι] (b : Π i, Basis (κ i) R
 (M i)) (x : Π i, M i) (p : Π i, κ i) : (Basis.piTensorProduct b).repr (tprod R 
x) p = ∏ i : ι, (b i).repr (x i) (p i)
参数：b : Π i, Basis (κ i) R (M i)；x : Π i, M i；p : Π i, κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Basis.piTensorProduct.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : ι → Typ
e u_3} {κ : ι → Type u_4} [inst : CommSemiring R]   [inst_1 : (i : ι) → AddCommM
onoid (M i)] [in…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `Finsupp.lcongr_symm`：lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ
[σ] N) : (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm
· 使用定理 `Module.Basis.map_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M
' : Type u_7} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M]…
· 使用定理 `Finsupp.basisSingleOne_repr`：∀ {R : Type u_1} {ι : Type u_3} [inst : Sem
iring R], Finsupp.basisSingleOne.repr = LinearEquiv.refl R (ι →₀ R)
· 使用定理 `LinearEquiv.trans_refl`：trans_refl : e.trans (refl S M₂) = e
· 使用定理 `PiTensorProduct.congr_tprod`：congr_tprod (f : Π i, s i ≃ₗ[R] t i) (m : Π
 i, s i) : congr f (tprod R m) = tprod R (fun (i : ι) => (f i) (m i))
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
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
theorem Basis.piTensorProduct_repr_tprod_apply [Fintype ι] (b : Π i, Basis (κ i) R (M i))
    (x : Π i, M i) (p : Π i, κ i) :
    (Basis.piTensorProduct b).repr (tprod R x) p = ∏ i : ι, (b i).repr (x i) (p i) := by
  rw [piTensorProduct, Subsingleton.elim (Fintype.ofFinite ι) ‹_›]
  simp

@[simp]
/-
**Basis.piTensorProduct_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Basis.piTensorProduct_apply [Finite ι] (b : Π i, Basis (κ i) R (M i)) (p :
 Π i, κ i) : Basis.piTensorProduct b p = ⨂ₜ[R] i, (b i) (p i)
参数：b : Π i, Basis (κ i) R (M i)；p : Π i, κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext_elem`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_12}
 [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (
b : Module.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Basis.piTensorProduct_repr_tprod_apply`：Basis.piTensorProduct_repr_tprod
_apply [Fintype ι] (b : Π i, Basis (κ i) R (M i)) (x : Π i, M i) (p : Π i, κ i) 
: (Basis.piTensorProduct b).…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Fintype.prod_ite_zero`：prod_ite_zero : (∏ i, if p i then f i else 0) = i
f forall i, p i then ∏ i, f i else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Basis.piTensorProduct_apply [Finite ι] (b : Π i, Basis (κ i) R (M i)) (p : Π i, κ i) :
    Basis.piTensorProduct b p = ⨂ₜ[R] i, (b i) (p i) := by
  have := Fintype.ofFinite ι
  classical
  refine (Basis.piTensorProduct b).ext_elem (fun q ↦ ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]

end PiTensorProduct

