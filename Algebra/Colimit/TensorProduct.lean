/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Colimit.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

/-!
# Tensor product with direct limit of finitely generated submodules

We show that if `M` and `P` are arbitrary modules and `N` is a finitely generated submodule
of a module `P`, then two elements of `N ⊗ M` have the same image in `P ⊗ M` if and only if
they already have the same image in `N' ⊗ M` for some finitely generated submodule `N' ≥ N`.
This is the theorem `Submodule.FG.exists_rTensor_fg_inclusion_eq`. The key facts used are
that every module is the direct limit of its finitely generated submodules and that tensor
product preserves colimits.
-/

public section

open TensorProduct

variable {R M P : Type*} [CommSemiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid P] [Module R P]

/-
**Submodule.FG.exists_rTensor_fg_inclusion_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.FG.exists_rTensor_fg_inclusion_eq {N : Submodule R P} (hN : N.FG
) {x y : N otimes[R] M} (eq : N.subtype.rTensor M x = N.subtype.rTensor M y) : e
xists N', N'.FG ∧ exists h : N <= N', (N.inclusion h).rTensor M x = (N.inclusion
 h).rTensor M y
参数：hN : N.FG；eq : N.subtype.rTensor M x = N.subtype.rTensor M y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Module.DirectLimit.exists_eq_of_of_eq`：exists_eq_of_of_eq {i x y} (h : o
f R ι G f i x = of R ι G f i y) : exists j hij, f i j hij x = f i j hij y
· 使用定理 `TensorProduct.instDirectedSystemCoeLinearMapIdRTensor`：∀ {R : Type u_1} 
[inst : CommSemiring R] {ι : Type u_2} [inst_1 : Preorder ι] {G : ι → Type u_3} 
  [inst_2 : (i : ι) → AddCommMonoid (G i)] …
· 使用定理 `Module.fgSystem.instDirectedSystemSubtypeSubmoduleFGMemValCoeLinearMapId
`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [inst_1 : AddCommMonoid M]
 [inst_2 : _root_.Module R M],   DirectedSystem (fun x2 => ↥↑x…
· 使用定理 `Module.fgSystem.instIsDirectedOrderSubtypeSubmoduleFG`：∀ (R : Type u_1) 
(M : Type u_2) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.M
odule R M],   IsDirectedOrder { N // N.FG }
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.directLimitLeft_rTensor_of`：directLimitLeft_rTensor_of {i 
: ι} (x : G i otimes[R] M) : directLimitLeft f M (LinearMap.rTensor M (of ..) x)
 = of _ _ _ (f ▷ M) _ x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.eq_toLinearMap_symm_comp`：eq_toLinearMap_symm_comp (f : M₃ -
>ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂) : f = e₁₂.symm.toLinearMap.comp g ↔ e₁₂.toLin
earMap.comp f = g
· 使用引理 `Module.fgSystem.equiv_comp_of`：equiv_comp_of (N : {N : Submodule R M // 
N.FG}) : (equiv R M).toLinearMap ∘ₗ of _ _ _ _ N = N.1.subtype
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Submodule.FG.exists_rTensor_fg_inclusion_eq {N : Submodule R P} (hN : N.FG)
    {x y : N ⊗[R] M} (eq : N.subtype.rTensor M x = N.subtype.rTensor M y) :
    ∃ N', N'.FG ∧ ∃ h : N ≤ N', (N.inclusion h).rTensor M x = (N.inclusion h).rTensor M y := by
  lift N to {N : Submodule R P // N.FG} using hN
  apply_fun (Module.fgSystem.equiv R P).symm.toLinearMap.rTensor M at eq
  apply_fun directLimitLeft _ _ at eq
  simp_rw [← LinearMap.rTensor_comp_apply, ← (LinearEquiv.eq_toLinearMap_symm_comp _ _).mpr
    (Module.fgSystem.equiv_comp_of N), directLimitLeft_rTensor_of] at eq
  have ⟨N', le, eq⟩ := Module.DirectLimit.exists_eq_of_of_eq eq
  exact ⟨_, N'.2, le, eq⟩
