/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, David Swinarski
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Local properties of modules and submodules

In this file, we show that several conditions on submodules can be checked on stalks.
-/

public section

open scoped nonZeroDivisors

variable {R M M₁ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid M₁] [Module R M₁]

section maximal

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommSemiring (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]
  (M₁ₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (M₁ₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (M₁ₚ P)]
  (f₁ : ∀ (P : Ideal R) [P.IsMaximal], M₁ →ₗ[R] M₁ₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f₁ P)]

/-
**Submodule.mem_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.mem_of_localization_maximal (m : M) (N : Submodule R M) (h : for
all (P : Ideal R) [P.IsMaximal], f P m in N.localized₀ P.primeCompl (f P)) : m i
n N
参数：m : M；N : Submodule R M；h : forall (P : Ideal R) [P.IsMaximal], f P m in N.lo
calized₀ P.primeCompl (f P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalizedModule.mk'_eq_mk'_iff`：∀ {R : Type u_1} [inst : CommSemiring 
R] {S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]  
 [inst_2 : AddCommMono…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] (S :
 Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_
2 : AddCommMono…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
-/
theorem Submodule.mem_of_localization_maximal (m : M) (N : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P m ∈ N.localized₀ P.primeCompl (f P)) :
    m ∈ N := by
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R M m)
  suffices I = ⊤ by simpa [I] using I.eq_top_iff_one.mp this
  refine Not.imp_symm I.exists_le_maximal fun ⟨P, hP, le⟩ ↦ ?_
  obtain ⟨a, ha, s, e⟩ := h P
  rw [← IsLocalizedModule.mk'_one P.primeCompl, IsLocalizedModule.mk'_eq_mk'_iff] at e
  obtain ⟨t, ht⟩ := e
  simp_rw [smul_smul] at ht
  exact (t * s).2 (le <| by apply ht ▸ smul_mem _ _ ha)

/-- Let `N₁ N₂ : Submodule R M`. If the localization of `N₁` at each maximal ideal `P` is
included in the localization of `N₂` at `P`, then `N₁ ≤ N₂`. -/
/-
**Submodule.le_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.le_of_localization_maximal {N₁ N₂ : Submodule R M} (h : forall (
P : Ideal R) [P.IsMaximal], N₁.localized₀ P.primeCompl (f P) <= N₂.localized₀ P.
primeCompl (f P)) : N₁ <= N₂
参数：h : forall (P : Ideal R) [P.IsMaximal], N₁.localized₀ P.primeCompl (f P) <= N
₂.localized₀ P.primeCompl (f P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Submodule.mem_of_localization_maximal`：Submodule.mem_of_localization_max
imal (m : M) (N : Submodule R M) (h : forall (P : Ideal R) [P.IsMaximal], f P m 
in N.localized₀ P.primeComp…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalizedModule.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] (S :
 Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_
2 : AddCommMono…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Let `N₁ N₂ : Submodule R M`. If the localization of `N₁` at each maximal ideal `
P` is
included in the localization of `N₂` at `P`, then `N₁ ≤ N₂`.
-/
theorem Submodule.le_of_localization_maximal {N₁ N₂ : Submodule R M}
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      N₁.localized₀ P.primeCompl (f P) ≤ N₂.localized₀ P.primeCompl (f P)) :
    N₁ ≤ N₂ :=
  fun m hm ↦ mem_of_localization_maximal _ f _ _ fun P hP ↦ h P ⟨m, hm, 1, by simp⟩

/-- Let `N₁ N₂ : Submodule R M`. If the localization of `N₁` at each maximal ideal `P` is equal to
the localization of `N₂` at `P`, then `N₁ = N₂`. -/
/-
**Submodule.eq_of_localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `N₁ N₂ : Submodule R M`. If the localization of `N₁` at each maximal ideal `
P` is equal to
the localization of `N₂` at `P`, then `N₁ = N₂`.
-/
theorem Submodule.eq_of_localization₀_maximal {N₁ N₂ : Submodule R M}
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      N₁.localized₀ P.primeCompl (f P) = N₂.localized₀ P.primeCompl (f P)) :
    N₁ = N₂ :=
  le_antisymm (Submodule.le_of_localization_maximal Mₚ f fun P _ ↦ (h P).le)
    (Submodule.le_of_localization_maximal Mₚ f fun P _ ↦ (h P).ge)

/-- A submodule is trivial if its localization at every maximal ideal is trivial. -/
/-
**Submodule.eq_bot_of_localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule is trivial if its localization at every maximal ideal is trivial.
-/
theorem Submodule.eq_bot_of_localization₀_maximal (N : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], N.localized₀ P.primeCompl (f P) = ⊥) :
    N = ⊥ :=
  Submodule.eq_of_localization₀_maximal Mₚ f fun P hP ↦ by simpa using h P
/-
**Submodule.eq_top_of_localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Submodule.eq_top_of_localization₀_maximal (N : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], N.localized₀ P.primeCompl (f P) = ⊤) :
    N = ⊤ :=
  Submodule.eq_of_localization₀_maximal Mₚ f fun P hP ↦ by simpa using h P
/-
**Module.eq_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.eq_of_localization_maximal (m m' : M) (h : forall (P : Ideal R) [P.
IsMaximal], f P m = f P m') : m = m'
参数：m m' : M；h : forall (P : Ideal R) [P.IsMaximal], f P m = f P m'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.ne_top_iff_one`：ne_top_iff_one : I != ⊤ ↔ (1 : α) ∉ I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsLocalizedModule.eq_iff_exists`：IsLocalizedModule.eq_iff_exists [IsLoca
lizedModule S f] {x₁ x₂} : f x₁ = f x₂ ↔ exists c : S, c • x₁ = c • x₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Module.eq_of_localization_maximal (m m' : M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P m = f P m') :
    m = m' := by
  rw [← one_smul R m, ← one_smul R m']
  by_contra ne
  have ⟨P, mP, le⟩ := (eqIdeal R m m').exists_le_maximal ((Ideal.ne_top_iff_one _).mpr ne)
  have ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists P.primeCompl _).mp (h P)
  exact s.2 (le hs)
/-
**Module.eq_zero_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.eq_zero_of_localization_maximal (m : M) (h : forall (P : Ideal R) [
P.IsMaximal], f P m = 0) : m = 0
参数：m : M；h : forall (P : Ideal R) [P.IsMaximal], f P m = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Module.eq_of_localization_maximal`：Module.eq_of_localization_maximal (m 
m' : M) (h : forall (P : Ideal R) [P.IsMaximal], f P m = f P m') : m = m'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
-/
theorem Module.eq_zero_of_localization_maximal (m : M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P m = 0) :
    m = 0 :=
  eq_of_localization_maximal _ f _ _ fun P _ ↦ by rw [h, map_zero]
/-
**LinearMap.eq_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.eq_of_localization_maximal (g g' : M ->ₗ[R] M₁) (h : forall (P :
 Ideal R) [P.IsMaximal], IsLocalizedModule.map P.primeCompl (f P) (f₁ P) g = IsL
ocalizedModule.map P.primeCompl (f P) (f₁ P) g') : g = g'
参数：g g' : M ->ₗ[R] M₁；h : forall (P : Ideal R) [P.IsMaximal], IsLocalizedModule.
map P.primeCompl (f P) (f₁ P) g = IsLocalizedModule.map P.primeCompl (f P) (f₁ P
) g'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Module.eq_of_localization_maximal`：Module.eq_of_localization_maximal (m 
m' : M) (h : forall (P : Ideal R) [P.IsMaximal], f P m = f P m') : m = m'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalizedModule.map_apply`：map_apply (h : M ->ₗ[R] N) (x) : map S f g 
h (f x) = g (h x)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem LinearMap.eq_of_localization_maximal (g g' : M →ₗ[R] M₁)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      IsLocalizedModule.map P.primeCompl (f P) (f₁ P) g =
      IsLocalizedModule.map P.primeCompl (f P) (f₁ P) g') :
    g = g' :=
  ext fun x ↦ Module.eq_of_localization_maximal _ f₁ _ _ fun P _ ↦ by
    simpa only [IsLocalizedModule.map_apply] using DFunLike.congr_fun (h P) (f P x)

include f in
/-
**Module.subsingleton_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.subsingleton_of_localization_maximal (h : forall (P : Ideal R) [P.I
sMaximal], Subsingleton (Mₚ P)) : Subsingleton M
参数：h : forall (P : Ideal R) [P.IsMaximal], Subsingleton (Mₚ P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `subsingleton_iff_forall_eq`：∀ {α : Sort u_1} (x : α), Subsingleton α ↔ ∀
 (y : α), y = x
· 使用定理 `Module.eq_of_localization_maximal`：Module.eq_of_localization_maximal (m 
m' : M) (h : forall (P : Ideal R) [P.IsMaximal], f P m = f P m') : m = m'
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem Module.subsingleton_of_localization_maximal
    (h : ∀ (P : Ideal R) [P.IsMaximal], Subsingleton (Mₚ P)) :
    Subsingleton M := by
  rw [subsingleton_iff_forall_eq 0]
  intro x
  exact Module.eq_of_localization_maximal Mₚ f x 0 fun _ _ ↦ Subsingleton.elim _ _
/-
**Submodule.eq_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.eq_of_localization_maximal {N₁ N₂ : Submodule R M} (h : forall (
P : Ideal R) [P.IsMaximal], N₁.localized' (Rₚ P) P.primeCompl (f P) = N₂.localiz
ed' (Rₚ P) P.primeCompl (f P)) : N₁ = N₂
参数：h : forall (P : Ideal R) [P.IsMaximal], N₁.localized' (Rₚ P) P.primeCompl (f 
P) = N₂.localized' (Rₚ P) P.primeCompl (f P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Submodule.eq_of_localization₀_maximal`：Submodule.eq_of_localization₀_max
imal {N₁ N₂ : Submodule R M} (h : forall (P : Ideal R) [P.IsMaximal], N₁.localiz
ed₀ P.primeCompl (f P) = N₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem Submodule.eq_of_localization_maximal {N₁ N₂ : Submodule R M}
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      N₁.localized' (Rₚ P) P.primeCompl (f P) = N₂.localized' (Rₚ P) P.primeCompl (f P)) :
    N₁ = N₂ :=
  eq_of_localization₀_maximal Mₚ f fun P _ ↦ congr(restrictScalars _ $(h P))
/-
**Submodule.eq_bot_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.eq_bot_of_localization_maximal (N : Submodule R M) (h : forall (
P : Ideal R) [P.IsMaximal], N.localized' (Rₚ P) P.primeCompl (f P) = ⊥) : N = ⊥
参数：N : Submodule R M；h : forall (P : Ideal R) [P.IsMaximal], N.localized' (Rₚ P)
 P.primeCompl (f P) = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Submodule.eq_of_localization_maximal`：Submodule.eq_of_localization_maxim
al {N₁ N₂ : Submodule R M} (h : forall (P : Ideal R) [P.IsMaximal], N₁.localized
' (Rₚ P) P.primeCompl (f P…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.localized'_bot`：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3}
 {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Ad
dCommMonoid M]…
-/
theorem Submodule.eq_bot_of_localization_maximal (N : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], N.localized' (Rₚ P) P.primeCompl (f P) = ⊥) :
    N = ⊥ :=
  Submodule.eq_of_localization_maximal Rₚ Mₚ f fun P hP ↦ by simpa using h P
/-
**Submodule.eq_top_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.eq_top_of_localization_maximal (N : Submodule R M) (h : forall (
P : Ideal R) [P.IsMaximal], N.localized' (Rₚ P) P.primeCompl (f P) = ⊤) : N = ⊤
参数：N : Submodule R M；h : forall (P : Ideal R) [P.IsMaximal], N.localized' (Rₚ P)
 P.primeCompl (f P) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Submodule.eq_of_localization_maximal`：Submodule.eq_of_localization_maxim
al {N₁ N₂ : Submodule R M} (h : forall (P : Ideal R) [P.IsMaximal], N₁.localized
' (Rₚ P) P.primeCompl (f P…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.localized'_top`：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3}
 {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Ad
dCommMonoid M]…
-/
theorem Submodule.eq_top_of_localization_maximal (N : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], N.localized' (Rₚ P) P.primeCompl (f P) = ⊤) :
    N = ⊤ :=
  Submodule.eq_of_localization_maximal Rₚ Mₚ f fun P hP ↦ by simpa using h P

end maximal

section span

open IsLocalizedModule LocalizedModule Ideal

variable (s : Set R) (span_eq : Ideal.span s = ⊤)
include span_eq

variable
  (Rₚ : ∀ _ : s, Type*)
  [∀ r : s, CommSemiring (Rₚ r)]
  [∀ r : s, Algebra R (Rₚ r)]
  [∀ r : s, IsLocalization.Away r.1 (Rₚ r)]
  (Mₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommMonoid (Mₚ r)]
  [∀ r : s, Module R (Mₚ r)]
  [∀ r : s, Module (Rₚ r) (Mₚ r)]
  [∀ r : s, IsScalarTower R (Rₚ r) (Mₚ r)]
  (f : ∀ r : s, M →ₗ[R] Mₚ r)
  [∀ r : s, IsLocalizedModule.Away r.1 (f r)]

/-
**Module.eq_of_isLocalized_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.eq_of_isLocalized_span (x y : M) (h : forall r : s, f r x = f r y) 
: x = y
参数：x y : M；h : forall r : s, f r x = f r y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ideal.exists_disjoint_powers_of_span_eq_top`：exists_disjoint_powers_of_s
pan_eq_top (s : Set α) (hs : span s = ⊤) (I : Ideal α) (hI : I != ⊤) : exists r 
in s, Disjoint (I : Set α) (Submo…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsLocalizedModule.eq_iff_exists`：IsLocalizedModule.eq_iff_exists [IsLoca
lizedModule S f] {x₁ x₂} : f x₁ = f x₂ ↔ exists c : S, c • x₁ = c • x₂
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
-/
theorem Module.eq_of_isLocalized_span (x y : M) (h : ∀ r : s, f r x = f r y) : x = y := by
  suffices Module.eqIdeal R x y = ⊤ by simpa [Module.eqIdeal] using (eq_top_iff_one _).mp this
  by_contra ne
  have ⟨r, hrs, disj⟩ := exists_disjoint_powers_of_span_eq_top s span_eq _ ne
  let r : s := ⟨r, hrs⟩
  have ⟨⟨_, n, rfl⟩, eq⟩ := (IsLocalizedModule.eq_iff_exists (.powers r.1) _).mp (h r)
  exact Set.disjoint_left.mp disj eq ⟨n, rfl⟩
/-
**Module.eq_zero_of_isLocalized_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.eq_zero_of_isLocalized_span (x : M) (h : forall r : s, f r x = 0) :
 x = 0
参数：x : M；h : forall r : s, f r x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.eq_of_isLocalized_span`：Module.eq_of_isLocalized_span (x y : M) (
h : forall r : s, f r x = f r y) : x = y
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
-/
theorem Module.eq_zero_of_isLocalized_span (x : M) (h : ∀ r : s, f r x = 0) : x = 0 :=
  eq_of_isLocalized_span s span_eq _ f x 0 <| by simpa only [map_zero] using h
/-
**Submodule.mem_of_isLocalized_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.mem_of_isLocalized_span {m : M} {N : Submodule R M} (h : forall 
r : s, f r m in N.localized₀ (.powers r.1) (f r)) : m in N
参数：h : forall r : s, f r m in N.localized₀ (.powers r.1) (f r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ideal.exists_disjoint_powers_of_span_eq_top`：exists_disjoint_powers_of_s
pan_eq_top (s : Set α) (hs : span s = ⊤) (I : Ideal α) (hI : I != ⊤) : exists r 
in s, Disjoint (I : Set α) (Submo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalizedModule.mk'_eq_mk'_iff`：∀ {R : Type u_1} [inst : CommSemiring 
R] {S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]  
 [inst_2 : AddCommMono…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] (S :
 Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_
2 : AddCommMono…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -
> a ∉ s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
-/
theorem Submodule.mem_of_isLocalized_span {m : M} {N : Submodule R M}
    (h : ∀ r : s, f r m ∈ N.localized₀ (.powers r.1) (f r)) : m ∈ N := by
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R M m)
  suffices I = ⊤ by simpa [I] using I.eq_top_iff_one.mp this
  by_contra! ne
  have ⟨r, hrs, disj⟩ := exists_disjoint_powers_of_span_eq_top s span_eq _ ne
  let r : s := ⟨r, hrs⟩
  obtain ⟨a, ha, t, e⟩ := h r
  rw [← IsLocalizedModule.mk'_one (.powers r.1), IsLocalizedModule.mk'_eq_mk'_iff] at e
  have ⟨u, hu⟩ := e
  simp_rw [smul_smul] at hu
  exact Set.disjoint_right.mp disj (u * t).2 (by apply hu ▸ smul_mem _ _ ha)
/-
**Submodule.le_of_isLocalized_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.le_of_isLocalized_span {N P : Submodule R M} (h : forall r : s, 
N.localized₀ (.powers r.1) (f r) <= P.localized₀ (.powers r.1) (f r)) : N <= P
参数：h : forall r : s, N.localized₀ (.powers r.1) (f r) <= P.localized₀ (.powers r
.1) (f r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_of_isLocalized_span`：Submodule.mem_of_isLocalized_span {m 
: M} {N : Submodule R M} (h : forall r : s, f r m in N.localized₀ (.powers r.1) 
(f r)) : m in N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalizedModule.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] (S :
 Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_
2 : AddCommMono…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Submodule.le_of_isLocalized_span {N P : Submodule R M}
    (h : ∀ r : s, N.localized₀ (.powers r.1) (f r) ≤ P.localized₀ (.powers r.1) (f r)) : N ≤ P :=
  fun m hm ↦ mem_of_isLocalized_span s span_eq _ f fun r ↦ h r ⟨m, hm, 1, by simp⟩
/-
**Submodule.eq_of_isLocalized** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Submodule.eq_of_isLocalized₀_span {N P : Submodule R M}
    (h : ∀ r : s, N.localized₀ (.powers r.1) (f r) = P.localized₀ (.powers r.1) (f r)) : N = P :=
  le_antisymm (le_of_isLocalized_span s span_eq _ _ fun r ↦ (h r).le)
    (le_of_isLocalized_span s span_eq _ _ fun r ↦ (h r).ge)
/-
**Submodule.eq_bot_of_isLocalized** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Submodule.eq_bot_of_isLocalized₀_span {N : Submodule R M}
    (h : ∀ r : s, N.localized₀ (.powers r.1) (f r) = ⊥) : N = ⊥ :=
  eq_of_isLocalized₀_span s span_eq Mₚ f fun _ ↦ by simp only [h, Submodule.localized₀_bot]
/-
**Submodule.eq_top_of_isLocalized** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Submodule.eq_top_of_isLocalized₀_span {N : Submodule R M}
    (h : ∀ r : s, N.localized₀ (.powers r.1) (f r) = ⊤) : N = ⊤ :=
  eq_of_isLocalized₀_span s span_eq Mₚ f fun _ ↦ by simp only [h, Submodule.localized₀_top]
/-
**Submodule.eq_of_isLocalized'_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   (s : Set R),   Ideal.span s = ⊤ →     ∀ 
(Rₚ : ↑s → Type u_4) [inst_3 : (r : ↑s) → CommSemiring (Rₚ r)] [inst_4 : (r : ↑s
) → Algebra R (Rₚ r)]       [inst_5 : ∀ (r : ↑s), IsLocalization.Away (↑r) (Rₚ r
)] (Mₚ : ↑s → Type u_5)       [inst_6 : (r : ↑s) → AddCommMonoid (Mₚ r)] [inst_7
 : (r : ↑s) → _root_.Module R (Mₚ r)]       [inst_8 : (r : ↑s) → _root_.Module (
Rₚ r) (Mₚ r)] [inst_9 : ∀ (r : ↑s), IsScalarTower R (Rₚ r) (Mₚ r)]       (f : (r
 : ↑s) → M →ₗ[R] Mₚ r) [inst_10 : ∀ (r : ↑s), IsLocalizedModule.Away (↑r) (f r)]
 {N P : Submodule R M},       (∀ (r : ↑s),           Submodule.localized' (Rₚ r)
 (Submonoid.powers ↑r) (f r) N =             Submodule.localized' (Rₚ r) (Submon
oid.powers ↑r) (f r) P) →         N = P
参数：s : Set R；Rₚ : ↑s → Type u_4；r : ↑s；Rₚ r；r : ↑s；Rₚ r；r : ↑s；↑r；Rₚ r；Mₚ : ↑s →
 Type u_5；r : ↑s；Mₚ r；r : ↑s；Mₚ r；r : ↑s；Rₚ r；Mₚ r；r : ↑s；Rₚ r；Mₚ r；f : (r : ↑s)
 → M →ₗ[R] Mₚ r；r : ↑s；↑r；f r；∀ (r : ↑s),           Submodule.localized' (Rₚ r) 
(Submonoid.powers ↑r) (f r) N =             Submodule.localized' (Rₚ r) (Submono
id.powers ↑r) (f r) P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.eq_of_isLocalized₀_span`：Submodule.eq_of_isLocalized₀_span {N 
P : Submodule R M} (h : forall r : s, N.localized₀ (.powers r.1) (f r) = P.local
ized₀ (.powers r.1) (f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem Submodule.eq_of_isLocalized'_span {N P : Submodule R M}
    (h : ∀ r, N.localized' (Rₚ r) (.powers r.1) (f r) = P.localized' (Rₚ r) (.powers r.1) (f r)) :
    N = P :=
  eq_of_isLocalized₀_span s span_eq _ f fun r ↦ congr(restrictScalars _ $(h r))
/-
**Submodule.eq_bot_of_isLocalized'_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   (s : Set R),   Ideal.span s = ⊤ →     ∀ 
(Rₚ : ↑s → Type u_4) [inst_3 : (r : ↑s) → CommSemiring (Rₚ r)] [inst_4 : (r : ↑s
) → Algebra R (Rₚ r)]       [inst_5 : ∀ (r : ↑s), IsLocalization.Away (↑r) (Rₚ r
)] (Mₚ : ↑s → Type u_5)       [inst_6 : (r : ↑s) → AddCommMonoid (Mₚ r)] [inst_7
 : (r : ↑s) → _root_.Module R (Mₚ r)]       [inst_8 : (r : ↑s) → _root_.Module (
Rₚ r) (Mₚ r)] [inst_9 : ∀ (r : ↑s), IsScalarTower R (Rₚ r) (Mₚ r)]       (f : (r
 : ↑s) → M →ₗ[R] Mₚ r) [inst_10 : ∀ (r : ↑s), IsLocalizedModule.Away (↑r) (f r)]
 {N : Submodule R M},       (∀ (r : ↑s), Submodule.localized' (Rₚ r) (Submonoid.
powers ↑r) (f r) N = ⊥) → N = ⊥
参数：s : Set R；Rₚ : ↑s → Type u_4；r : ↑s；Rₚ r；r : ↑s；Rₚ r；r : ↑s；↑r；Rₚ r；Mₚ : ↑s →
 Type u_5；r : ↑s；Mₚ r；r : ↑s；Mₚ r；r : ↑s；Rₚ r；Mₚ r；r : ↑s；Rₚ r；Mₚ r；f : (r : ↑s)
 → M →ₗ[R] Mₚ r；r : ↑s；↑r；f r；∀ (r : ↑s), Submodule.localized' (Rₚ r) (Submonoid
.powers ↑r) (f r) N = ⊥。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.eq_of_isLocalized'_span`：∀ {R : Type u_1} {M : Type u_2} [inst
 : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (s 
: Set R),   Ideal.span …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.localized'_bot`：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3}
 {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Ad
dCommMonoid M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Submodule.eq_bot_of_isLocalized'_span {N : Submodule R M}
    (h : ∀ r : s, N.localized' (Rₚ r) (.powers r.1) (f r) = ⊥) : N = ⊥ :=
  eq_of_isLocalized'_span s span_eq Rₚ Mₚ f fun _ ↦ by simp only [h, Submodule.localized'_bot]
/-
**Submodule.eq_top_of_isLocalized'_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   (s : Set R),   Ideal.span s = ⊤ →     ∀ 
(Rₚ : ↑s → Type u_4) [inst_3 : (r : ↑s) → CommSemiring (Rₚ r)] [inst_4 : (r : ↑s
) → Algebra R (Rₚ r)]       [inst_5 : ∀ (r : ↑s), IsLocalization.Away (↑r) (Rₚ r
)] (Mₚ : ↑s → Type u_5)       [inst_6 : (r : ↑s) → AddCommMonoid (Mₚ r)] [inst_7
 : (r : ↑s) → _root_.Module R (Mₚ r)]       [inst_8 : (r : ↑s) → _root_.Module (
Rₚ r) (Mₚ r)] [inst_9 : ∀ (r : ↑s), IsScalarTower R (Rₚ r) (Mₚ r)]       (f : (r
 : ↑s) → M →ₗ[R] Mₚ r) [inst_10 : ∀ (r : ↑s), IsLocalizedModule.Away (↑r) (f r)]
 {N : Submodule R M},       (∀ (r : ↑s), Submodule.localized' (Rₚ r) (Submonoid.
powers ↑r) (f r) N = ⊤) → N = ⊤
参数：s : Set R；Rₚ : ↑s → Type u_4；r : ↑s；Rₚ r；r : ↑s；Rₚ r；r : ↑s；↑r；Rₚ r；Mₚ : ↑s →
 Type u_5；r : ↑s；Mₚ r；r : ↑s；Mₚ r；r : ↑s；Rₚ r；Mₚ r；r : ↑s；Rₚ r；Mₚ r；f : (r : ↑s)
 → M →ₗ[R] Mₚ r；r : ↑s；↑r；f r；∀ (r : ↑s), Submodule.localized' (Rₚ r) (Submonoid
.powers ↑r) (f r) N = ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.eq_of_isLocalized'_span`：∀ {R : Type u_1} {M : Type u_2} [inst
 : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (s 
: Set R),   Ideal.span …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.localized'_top`：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3}
 {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Ad
dCommMonoid M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Submodule.eq_top_of_isLocalized'_span {N : Submodule R M}
    (h : ∀ r : s, N.localized' (Rₚ r) (.powers r.1) (f r) = ⊤) : N = ⊤ :=
  eq_of_isLocalized'_span s span_eq Rₚ Mₚ f fun _ ↦ by simp only [h, Submodule.localized'_top]

end span

