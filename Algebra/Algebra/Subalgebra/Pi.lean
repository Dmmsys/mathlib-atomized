/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.Pi

/-!
# Products of subalgebras

In this file we define the product of subalgebras as a subalgebra of the product algebra.

## Main definitions

* `Subalgebra.pi`: the product of subalgebras.
-/

@[expose] public section

open Algebra

namespace Subalgebra
variable {ι R : Type*} {S : ι → Type*} [CommSemiring R] [∀ i, Semiring (S i)] [∀ i, Algebra R (S i)]
  {s : Set ι} {t t₁ t₂ : ∀ i, Subalgebra R (S i)} {x : ∀ i, S i}

/-- The product of subalgebras as a subalgebra. -/
@[simps coe toSubsemiring]
/-
**Subalgebra.pi** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：pi (s : Set ι) (t : forall i, Subalgebra R (S i)) : Subalgebra R (Π i, S i
) where __
参数：s : Set ι；t : forall i, Subalgebra R (S i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of subalgebras as a subalgebra.
-/
def pi (s : Set ι) (t : ∀ i, Subalgebra R (S i)) : Subalgebra R (Π i, S i) where
  __ := Submodule.pi s fun i ↦ (t i).toSubmodule
  mul_mem' hx hy i hi := (t i).mul_mem (hx i hi) (hy i hi)
  algebraMap_mem' _ i _ := (t i).algebraMap_mem _
/-
**Subalgebra.mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {S : ι → Type u_3} [inst : CommSemiring R]
 [inst_1 : (i : ι) → Semiring (S i)]   [inst_2 : (i : ι) → Algebra R (S i)] {s :
 Set ι} {t : (i : ι) → Subalgebra R (S i)} {x : (i : ι) → S i},   x ∈ Subalgebra
.pi s t ↔ ∀ i ∈ s, x i ∈ t i
参数：i : ι；S i；i : ι；S i；i : ι；S i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_pi : x ∈ pi s t ↔ ∀ i ∈ s, x i ∈ t i := .rfl

open Subalgebra in
/-
**Subalgebra.pi_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {S : ι → Type u_3} [inst : CommSemiring R]
 [inst_1 : (i : ι) → Semiring (S i)]   [inst_2 : (i : ι) → Algebra R (S i)] {s :
 Set ι} {t : (i : ι) → Subalgebra R (S i)},   Subalgebra.toSubmodule (Subalgebra
.pi s t) = Submodule.pi s fun i => Subalgebra.toSubmodule (t i)
参数：i : ι；S i；i : ι；S i；i : ι；S i；Subalgebra.pi s t；t i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pi_toSubmodule : toSubmodule (pi s t) = .pi s fun i ↦ (t i).toSubmodule := rfl

@[simp]
/-
**Subalgebra.pi_top** 是 Mathlib 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：pi_top (s : Set ι) : pi s (fun i => (⊤ : Subalgebra R (S i))) = ⊤
参数：s : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.pi_univ`：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = 
univ
-/
lemma pi_top (s : Set ι) : pi s (fun i ↦ (⊤ : Subalgebra R (S i))) = ⊤ :=
  SetLike.coe_injective <| Set.pi_univ _
/-
**Subalgebra.pi_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {S : ι → Type u_3} [inst : CommSemiring R]
 [inst_1 : (i : ι) → Semiring (S i)]   [inst_2 : (i : ι) → Algebra R (S i)] {s :
 Set ι} {t₁ t₂ : (i : ι) → Subalgebra R (S i)},   (∀ i ∈ s, t₁ i ≤ t₂ i) → Subal
gebra.pi s t₁ ≤ Subalgebra.pi s t₂
参数：i : ι；S i；i : ι；S i；i : ι；S i；∀ i ∈ s, t₁ i ≤ t₂ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pi_mono`：pi_mono (h : forall i in s, t₁ i subseteq t₂ i) : pi s t₁ s
ubseteq pi s t₂
-/
@[gcongr] lemma pi_mono (h : ∀ i ∈ s, t₁ i ≤ t₂ i) : pi s t₁ ≤ pi s t₂ := Set.pi_mono h
/-
**Subalgebra.center_pi** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {S : ι → Type u_3} [inst : CommSemiring R]
 [inst_1 : (i : ι) → Semiring (S i)]   [inst_2 : (i : ι) → Algebra R (S i)],   S
ubalgebra.center R ((i : ι) → S i) = Subalgebra.pi Set.univ fun i => Subalgebra.
center R (S i)
参数：i : ι；S i；i : ι；S i；(i : ι) → S i；S i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_pi`：∀ {ι : Type u_2} {A : ι → Type u_3} [inst : (i : ι) → Mul
 (A i)],   Set.center ((i : ι) → A i) = Set.univ.pi fun i => Set.center (A i)
-/
protected theorem center_pi : center R (Π i, S i) = pi .univ fun i ↦ center R (S i) :=
  SetLike.coe_injective Set.center_pi

end Subalgebra

