/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.RingTheory.Ideal.Operations

/-!

# Lemmas for action of ideals on submodules of `Finsupp`

-/

public section

variable (R : Type*) [CommRing R]

/-
**Finsupp.submodule_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finsupp.submodule_smul {M : Type*} [AddCommGroup M] [Module R M] (ι : Type
*) (p : ι -> Submodule R M) (I : Ideal R) : Finsupp.submodule (fun i => I • p i)
 = I • Finsupp.submodule p
参数：ι : Type*；p : ι -> Submodule R M；I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.submodule_eq_iSup`：submodule_eq_iSup (p : α -> Submodule R M) : 
Finsupp.submodule p = ⨆ i, Submodule.map (Finsupp.lsingle i) (p i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.map_smul''`：map_smul'' (f : M ->ₗ[R] M') : (I • N).map f = I •
 N.map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Finsupp.submodule_smul {M : Type*} [AddCommGroup M] [Module R M]
    (ι : Type*) (p : ι → Submodule R M) (I : Ideal R) :
    Finsupp.submodule (fun i ↦ I • p i) = I • Finsupp.submodule p := by
  simp only [Finsupp.submodule_eq_iSup, Submodule.map_smul'', ← Submodule.smul_iSup]
