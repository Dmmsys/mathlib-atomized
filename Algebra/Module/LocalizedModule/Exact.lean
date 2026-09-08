/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Localization of modules is an exact functor

## Main definitions

- `LocalizedModule.map_exact`: Localization of modules is an exact functor.
- `IsLocalizedModule.map_exact`: A variant expressed in terms of `IsLocalizedModule`.

-/

public section

section

open IsLocalizedModule Function Submonoid

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {M₀ M₀'} [AddCommMonoid M₀] [AddCommMonoid M₀'] [Module R M₀] [Module R M₀']
variable (f₀ : M₀ →ₗ[R] M₀') [IsLocalizedModule S f₀]
variable {M₁ M₁'} [AddCommMonoid M₁] [AddCommMonoid M₁'] [Module R M₁] [Module R M₁']
variable (f₁ : M₁ →ₗ[R] M₁') [IsLocalizedModule S f₁]
variable {M₂ M₂'} [AddCommMonoid M₂] [AddCommMonoid M₂'] [Module R M₂] [Module R M₂']
variable (f₂ : M₂ →ₗ[R] M₂') [IsLocalizedModule S f₂]

/-- Localization of modules is an exact functor, proven here for `LocalizedModule`.
See `IsLocalizedModule.map_exact` for the more general version. -/
/-
**LocalizedModule.map_exact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalizedModule.map_exact (g : M₀ ->ₗ[R] M₁) (h : M₁ ->ₗ[R] M₂) (ex : Exac
t g h) : Exact (map S (mkLinearMap S M₀) (mkLinearMap S M₁) g) (map S (mkLinearM
ap S M₁) (mkLinearMap S M₂) h)
参数：g : M₀ ->ₗ[R] M₁；h : M₁ ->ₗ[R] M₂；ex : Exact g h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LocalizedModule.induction_on`：induction_on {β : LocalizedModule S M -> P
rop} (h : forall (m : M) (s : S), β (mk m s)) : forall x : LocalizedModule S M, 
β x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.exists`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∃ x, q x) ↔ ∃ a, ∃ (b : p a), q ⟨a, b⟩
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LocalizedModule.zero_mk`：zero_mk (s : S) : mk (0 : M) s = 0
· 使用引理 `IsLocalizedModule.map_LocalizedModules`：map_LocalizedModules (g : M₀ ->ₗ
[R] M₁) (m : M₀) (s : S) : ((map S (mkLinearMap S M₀) (mkLinearMap S M₁)) g) (Lo
calizedModule.mk m s) = Loca…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `Submonoid.mk_smul`：mk_smul (g : M') (hg : g in S) (a : α) : (⟨g, hg⟩ : S
) • a = g • a
· 使用定理 `LocalizedModule.mk_cancel_common_left`：mk_cancel_common_left (s' s : S) 
(m : M) : mk (s' • m) (s' * s) = mk m s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Localization of modules is an exact functor, proven here for `LocalizedModule`.
See `IsLocalizedModule.map_exact` for the more general version.
-/
lemma LocalizedModule.map_exact (g : M₀ →ₗ[R] M₁) (h : M₁ →ₗ[R] M₂) (ex : Exact g h) :
    Exact (map S (mkLinearMap S M₀) (mkLinearMap S M₁) g)
    (map S (mkLinearMap S M₁) (mkLinearMap S M₂) h) :=
  fun y ↦ Iff.intro
    (induction_on
      (fun m s hy ↦ by
        rw [map_LocalizedModules, ← zero_mk 1, mk_eq, one_smul, smul_zero] at hy
        obtain ⟨a, aS, ha⟩ := Subtype.exists.1 hy
        rw [smul_zero, mk_smul, ← map_smul, ex (a • m)] at ha
        rcases ha with ⟨x, hx⟩
        use mk x (⟨a, aS⟩ * s)
        rw [map_LocalizedModules, hx, ← mk_cancel_common_left ⟨a, aS⟩ s m, mk_smul])
      y)
    fun ⟨x, hx⟩ ↦ by
      revert hx
      refine induction_on (fun m s hx ↦ ?_) x
      rw [← hx, map_LocalizedModules, map_LocalizedModules, (ex (g m)).2 ⟨m, rfl⟩, zero_mk]

/-- Localization of modules is an exact functor. -/
/-
**IsLocalizedModule.map_exact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.map_exact (g : M₀ ->ₗ[R] M₁) (h : M₁ ->ₗ[R] M₂) (ex : Fu
nction.Exact g h) : Function.Exact (map S f₀ f₁ g) (map S f₁ f₂ h)
参数：g : M₀ ->ₗ[R] M₁；h : M₁ ->ₗ[R] M₂；ex : Function.Exact g h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Exact.of_ladder_linearEquiv_of_exact`：of_ladder_linearEquiv_of_
exact (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃) (H : Exact f₁₂
 f₂₃) : Exact g₁₂ g₂₃
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsLocalizedModule.map_iso_commute`：map_iso_commute (g : M₀ ->ₗ[R] M₁) : 
(map S f₀ f₁) g ∘ₗ (iso S f₀) = (iso S f₁) ∘ₗ (map S (mkLinearMap S M₀) (mkLinea
rMap S M₁)) g
· 使用引理 `LocalizedModule.map_exact`：LocalizedModule.map_exact (g : M₀ ->ₗ[R] M₁) 
(h : M₁ ->ₗ[R] M₂) (ex : Exact g h) : Exact (map S (mkLinearMap S M₀) (mkLinearM
ap S M₁) g) (ma…

--- 原说明 ---
Localization of modules is an exact functor.
-/
theorem IsLocalizedModule.map_exact (g : M₀ →ₗ[R] M₁) (h : M₁ →ₗ[R] M₂) (ex : Function.Exact g h) :
    Function.Exact (map S f₀ f₁ g) (map S f₁ f₂ h) :=
  Function.Exact.of_ladder_linearEquiv_of_exact
    (map_iso_commute S f₀ f₁ g) (map_iso_commute S f₁ f₂ h) (LocalizedModule.map_exact S g h ex)

end

