/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker

/-!
# The submodule of elements `x : M` such that `f x = g x`

## Main declarations

* `LinearMap.eqLocus`: the submodule of elements `x : M` such that `f x = g x`

## Tags
linear algebra, vector space, module

-/

@[expose] public section

variable {R : Type*} {R₂ : Type*}
variable {M : Type*} {M₂ : Type*}

/-! ### Properties of linear maps -/


namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]

open Submodule

variable {τ₁₂ : R →+* R₂}

section

/-- A linear map version of `AddMonoidHom.eqLocusM` -/
/-
**LinearMap.eqLocus** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：eqLocus (f g : M ->ₛₗ[τ₁₂] M₂) : Submodule R M
参数：f g : M ->ₛₗ[τ₁₂] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map version of `AddMonoidHom.eqLocusM`
-/
def eqLocus (f g : M →ₛₗ[τ₁₂] M₂) : Submodule R M :=
  { (f : M →+ M₂).eqLocusM g with
    carrier := { x | f x = g x }
    smul_mem' := fun {r} {x} (hx : _ = _) => show _ = _ by
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
      simpa only [map_smulₛₗ _] using congr_arg (τ₁₂ r • ·) hx }

@[simp]
/-
**LinearMap.mem_eqLocus** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mem_eqLocus {x : M} {f g : M ->ₛₗ[τ₁₂] M₂} : x in eqLocus f g ↔ f x = g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_eqLocus {x : M} {f g : M →ₛₗ[τ₁₂] M₂} : x ∈ eqLocus f g ↔ f x = g x :=
  Iff.rfl
/-
**LinearMap.eqLocus_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eqLocus_toAddSubmonoid (f g : M ->ₛₗ[τ₁₂] M₂) : (eqLocus f g).toAddSubmono
id = (f : M ->+ M₂).eqLocusM g
参数：f g : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqLocus_toAddSubmonoid (f g : M →ₛₗ[τ₁₂] M₂) :
    (eqLocus f g).toAddSubmonoid = (f : M →+ M₂).eqLocusM g :=
  rfl

@[simp]
/-
**LinearMap.eqLocus_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eqLocus_eq_top {f g : M ->ₛₗ[τ₁₂] M₂} : eqLocus f g = ⊤ ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eqLocus_eq_top {f g : M →ₛₗ[τ₁₂] M₂} : eqLocus f g = ⊤ ↔ f = g := by
  simp [SetLike.ext_iff, DFunLike.ext_iff]

@[simp]
/-
**LinearMap.eqLocus_same** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eqLocus_same (f : M ->ₛₗ[τ₁₂] M₂) : eqLocus f f = ⊤
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.eqLocus_eq_top`：eqLocus_eq_top {f g : M ->ₛₗ[τ₁₂] M₂} : eqLocu
s f g = ⊤ ↔ f = g
-/
theorem eqLocus_same (f : M →ₛₗ[τ₁₂] M₂) : eqLocus f f = ⊤ := eqLocus_eq_top.2 rfl
/-
**LinearMap.le_eqLocus** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：le_eqLocus {f g : M ->ₛₗ[τ₁₂] M₂} {S : Submodule R M} : S <= eqLocus f g ↔
 Set.EqOn f g S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_eqLocus {f g : M →ₛₗ[τ₁₂] M₂} {S : Submodule R M} :
    S ≤ eqLocus f g ↔ Set.EqOn f g S :=
  Iff.rfl
/-
**LinearMap.eqOn_eqLocus** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eqOn_eqLocus {f g : M ->ₛₗ[τ₁₂] M₂} : Set.EqOn f g (eqLocus f g)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqOn_eqLocus {f g : M →ₛₗ[τ₁₂] M₂} :
    Set.EqOn f g (eqLocus f g) :=
  fun _ h ↦ h

variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

include τ₁₂ in
/-
**LinearMap.eqOn_sup** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eqOn_sup {f g : F} {S T : Submodule R M} (hS : Set.EqOn f g S) (hT : Set.E
qOn f g T) : Set.EqOn f g ↑(S ⊔ T)
参数：hS : Set.EqOn f g S；hT : Set.EqOn f g T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.coe_coe`：coe_coe {F : Type*} [FunLike F M M₃] [SemilinearMapCl
ass F σ M M₃] {f : F} : ⇑(f : M ->ₛₗ[σ] M₃) = f
· 使用定理 `LinearMap.le_eqLocus`：le_eqLocus {f g : M ->ₛₗ[τ₁₂] M₂} {S : Submodule R
 M} : S <= eqLocus f g ↔ Set.EqOn f g S
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
-/
theorem eqOn_sup {f g : F} {S T : Submodule R M}
    (hS : Set.EqOn f g S) (hT : Set.EqOn f g T) :
    Set.EqOn f g ↑(S ⊔ T) := by
  rw [← LinearMap.coe_coe (f := f), ← LinearMap.coe_coe (f := g), ← le_eqLocus] at hS hT ⊢
  exact sup_le hS hT

include τ₁₂ in
/-
**LinearMap.ext_on_codisjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ext_on_codisjoint {f g : F} {S T : Submodule R M} (hST : Codisjoint S T) (
hS : Set.EqOn f g S) (hT : Set.EqOn f g T) : f = g
参数：hST : Codisjoint S T；hS : Set.EqOn f g S；hT : Set.EqOn f g T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `LinearMap.eqOn_sup`：eqOn_sup {f g : F} {S T : Submodule R M} (hS : Set.E
qOn f g S) (hT : Set.EqOn f g T) : Set.EqOn f g ↑(S ⊔ T)
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Codisjoint.eq_top`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → a ⊔ b = ⊤
-/
theorem ext_on_codisjoint {f g : F} {S T : Submodule R M} (hST : Codisjoint S T)
    (hS : Set.EqOn f g S) (hT : Set.EqOn f g T) : f = g :=
  DFunLike.ext _ _ fun _ ↦ eqOn_sup hS hT <| hST.eq_top.symm ▸ trivial

end

end AddCommMonoid

section Ring

variable [Ring R] [Ring R₂]
variable [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂}

open Submodule

/-
**LinearMap.eqLocus_eq_ker_sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eqLocus_eq_ker_sub (f g : M ->ₛₗ[τ₁₂] M₂) : eqLocus f g = ker (f - g)
参数：f g : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
-/
theorem eqLocus_eq_ker_sub (f g : M →ₛₗ[τ₁₂] M₂) : eqLocus f g = ker (f - g) :=
  SetLike.ext fun _ => sub_eq_zero.symm

end Ring

end LinearMap

