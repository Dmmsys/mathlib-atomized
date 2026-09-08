/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Spectrum.Prime.Module

/-!

# Krull Dimension of Module

In this file we define `Module.supportDim R M` for an `R`-module `M` as
the krull dimension of its support. It is equal to the krull dimension of `R / Ann M` when
`M` is finitely generated.

-/

@[expose] public section

variable (R : Type*) [CommRing R]

variable (M : Type*) [AddCommGroup M] [Module R M] (N : Type*) [AddCommGroup N] [Module R N]

namespace Module

open Order

/-- The krull dimension of module, defined as `krullDim` of its support. -/
/-
**Module.supportDim** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：supportDim : WithBot Nat∞
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The krull dimension of module, defined as `krullDim` of its support.
-/
noncomputable def supportDim : WithBot ℕ∞ :=
  krullDim (Module.support R M)

@[nontriviality]
/-
**Module.supportDim_eq_bot_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：supportDim_eq_bot_of_subsingleton [Subsingleton M] : supportDim R M = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma supportDim_eq_bot_of_subsingleton [Subsingleton M] : supportDim R M = ⊥ := by
  simpa [supportDim, support_eq_empty_iff]
/-
**Module.supportDim_ne_bot_of_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：supportDim_ne_bot_of_nontrivial [Nontrivial M] : supportDim R M != ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用引理 `Module.nonempty_support_of_nontrivial`：Module.nonempty_support_of_nontri
vial [Nontrivial M] : (Module.support R M).Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma supportDim_ne_bot_of_nontrivial [Nontrivial M] : supportDim R M ≠ ⊥ := by
  have : Nonempty (Module.support R M) := nonempty_support_of_nontrivial.to_subtype
  simp [supportDim]
/-
**Module.supportDim_eq_bot_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：supportDim_eq_bot_iff_subsingleton : supportDim R M = ⊥ ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma supportDim_eq_bot_iff_subsingleton : supportDim R M = ⊥ ↔ Subsingleton M := by
  simp [supportDim, krullDim_eq_bot_iff, support_eq_empty_iff]
/-
**Module.supportDim_ne_bot_iff_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：supportDim_ne_bot_iff_nontrivial : supportDim R M != ⊥ ↔ Nontrivial M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma supportDim_ne_bot_iff_nontrivial : supportDim R M ≠ ⊥ ↔ Nontrivial M := by
  simp [supportDim, krullDim_eq_bot_iff, support_eq_empty_iff, not_subsingleton_iff_nontrivial]
/-
**Module.supportDim_eq_ringKrullDim_quotient_annihilator** 是 Mathlib 中的一个引理，位于命名
空间 `Module`。
形式化陈述：supportDim_eq_ringKrullDim_quotient_annihilator [Module.Finite R M] : supp
ortDim R M = ringKrullDim (R ⧸ annihilator R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.support_eq_zeroLocus`：Module.support_eq_zeroLocus : Module.suppor
t R M = zeroLocus (Module.annihilator R M)
· 使用引理 `ringKrullDim_quotient`：ringKrullDim_quotient (I : Ideal R) : ringKrullDi
m (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus (R
-/
lemma supportDim_eq_ringKrullDim_quotient_annihilator [Module.Finite R M] :
    supportDim R M = ringKrullDim (R ⧸ annihilator R M) := by
  simp only [supportDim]
  rw [support_eq_zeroLocus, ringKrullDim_quotient]
/-
**Module.supportDim_self_eq_ringKrullDim** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：supportDim_self_eq_ringKrullDim : supportDim R R = ringKrullDim R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.annihilator_eq_bot`：Module.annihilator_eq_bot {R M} [Ring R] [Add
CommGroup M] [Module R M] : Module.annihilator R M = ⊥ ↔ FaithfulSMul R M
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.supportDim_eq_ringKrullDim_quotient_annihilator`：supportDim_eq_ri
ngKrullDim_quotient_annihilator [Module.Finite R M] : supportDim R M = ringKrull
Dim (R ⧸ annihilator R M)
· 使用定理 `RingEquiv.ringKrullDim`：∀ {R : Type u_1} {S : Type u_2} [inst : CommSemi
ring R] [inst_1 : CommSemiring S] (e : R ≃+* S),   ringKrullDim R = ringKrullDim
 S
-/
lemma supportDim_self_eq_ringKrullDim : supportDim R R = ringKrullDim R := by
  have : annihilator R R = ⊥ :=
    annihilator_eq_bot.mpr ((faithfulSMul_iff_algebraMap_injective R R).mpr fun {a₁ a₂} a ↦ a)
  rw [supportDim_eq_ringKrullDim_quotient_annihilator, this]
  exact (RingEquiv.ringKrullDim (RingEquiv.quotientBot R))
/-
**Module.supportDim_le_ringKrullDim** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：supportDim_le_ringKrullDim : supportDim R M <= ringKrullDim R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.krullDim_le_of_strictMono`：krullDim_le_of_strictMono (f : α -> β) 
(hf : StrictMono f) : krullDim α <= krullDim β
-/
lemma supportDim_le_ringKrullDim : supportDim R M ≤ ringKrullDim R :=
  krullDim_le_of_strictMono (fun a ↦ a) fun {_ _} lt ↦ lt

variable {R M N}
/-
**Module.supportDim_quotient_eq_ringKrullDim** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：supportDim_quotient_eq_ringKrullDim (I : Ideal R) : supportDim R (R ⧸ I) =
 ringKrullDim (R ⧸ I)
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.supportDim_eq_ringKrullDim_quotient_annihilator`：supportDim_eq_ri
ngKrullDim_quotient_annihilator [Module.Finite R M] : supportDim R M = ringKrull
Dim (R ⧸ annihilator R M)
· 使用定理 `Ideal.annihilator_quotient`：∀ {R : Type u_1} [inst : Ring R] {I : Ideal 
R} [I.IsTwoSided], Module.annihilator R (R ⧸ I) = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma supportDim_quotient_eq_ringKrullDim (I : Ideal R) :
    supportDim R (R ⧸ I) = ringKrullDim (R ⧸ I) := by
  rw [supportDim_eq_ringKrullDim_quotient_annihilator, Ideal.annihilator_quotient]
/-
**Module.supportDim_le_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：supportDim_le_of_injective (f : M ->ₗ[R] N) (h : Function.Injective f) : s
upportDim R M <= supportDim R N
参数：f : M ->ₗ[R] N；h : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.krullDim_le_of_strictMono`：krullDim_le_of_strictMono (f : α -> β) 
(hf : StrictMono f) : krullDim α <= krullDim β
· 使用引理 `Module.support_subset_of_injective`：Module.support_subset_of_injective (
hf : Function.Injective f) : Module.support R M subseteq Module.support R N
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma supportDim_le_of_injective (f : M →ₗ[R] N) (h : Function.Injective f) :
    supportDim R M ≤ supportDim R N :=
  krullDim_le_of_strictMono (fun a ↦ ⟨a.1, Module.support_subset_of_injective f h a.2⟩)
    (fun {_ _} lt ↦ lt)
/-
**Module.supportDim_le_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：supportDim_le_of_surjective (f : M ->ₗ[R] N) (h : Function.Surjective f) :
 supportDim R N <= supportDim R M
参数：f : M ->ₗ[R] N；h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Order.krullDim_le_of_strictMono`：krullDim_le_of_strictMono (f : α -> β) 
(hf : StrictMono f) : krullDim α <= krullDim β
· 使用引理 `Module.support_subset_of_surjective`：Module.support_subset_of_surjective
 (hf : Function.Surjective f) : Module.support R N subseteq Module.support R M
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma supportDim_le_of_surjective (f : M →ₗ[R] N) (h : Function.Surjective f) :
    supportDim R N ≤ supportDim R M :=
  krullDim_le_of_strictMono (fun a ↦ ⟨a.1, Module.support_subset_of_surjective f h a.2⟩)
    (fun {_ _} lt ↦ lt)
/-
**Module.supportDim_eq_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：supportDim_eq_of_equiv (e : M ≃ₗ[R] N) : supportDim R M = supportDim R N
参数：e : M ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Module.supportDim_le_of_injective`：supportDim_le_of_injective (f : M ->ₗ
[R] N) (h : Function.Injective f) : supportDim R M <= supportDim R N
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用引理 `Module.supportDim_le_of_surjective`：supportDim_le_of_surjective (f : M -
>ₗ[R] N) (h : Function.Surjective f) : supportDim R N <= supportDim R M
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
-/
lemma supportDim_eq_of_equiv (e : M ≃ₗ[R] N) :
    supportDim R M = supportDim R N :=
  le_antisymm (supportDim_le_of_injective e e.injective)
    (supportDim_le_of_surjective e e.surjective)

end Module

open Ideal IsLocalRing

/-
**support_of_supportDim_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：support_of_supportDim_eq_zero [IsLocalRing R] (dim : Module.supportDim R N
 = 0) : Module.support R N = PrimeSpectrum.zeroLocus (maximalIdeal R)
参数：dim : Module.supportDim R N = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.supportDim_ne_bot_iff_nontrivial`：supportDim_ne_bot_iff_nontrivia
l : supportDim R M != ⊥ ↔ Nontrivial M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用引理 `PrimeSpectrum.zeroLocus_eq_singleton`：zeroLocus_eq_singleton (m : Ideal 
R) [m.IsMaximal] : zeroLocus m = {⟨m, inferInstance⟩}
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `IsLocalRing.le_maximalIdeal`：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤)
 : J <= maximalIdeal R
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `IsLocalRing.closedPoint_mem_support`：IsLocalRing.closedPoint_mem_support
 [IsLocalRing R] [Nontrivial M] : IsLocalRing.closedPoint R in Module.support R 
M
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
-/
lemma support_of_supportDim_eq_zero [IsLocalRing R]
    (dim : Module.supportDim R N = 0) :
    Module.support R N = PrimeSpectrum.zeroLocus (maximalIdeal R) := by
  let _ : Nontrivial N := by simp [← Module.supportDim_ne_bot_iff_nontrivial R, dim]
  rw [PrimeSpectrum.zeroLocus_eq_singleton]
  apply le_antisymm
  · intro p hp
    by_contra nmem
    push _ ∈ _ at nmem
    have : p < ⟨maximalIdeal R, IsMaximal.isPrime' (maximalIdeal R)⟩ :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal IsPrime.ne_top') nmem
    have : Module.supportDim R N > 0 := by
      simp only [Module.supportDim, gt_iff_lt, Order.krullDim_pos_iff, Subtype.exists,
        Subtype.mk_lt_mk, exists_prop]
      use p
      simpa [hp] using! ⟨_, IsLocalRing.closedPoint_mem_support R N, this⟩
    exact (ne_of_lt this) dim.symm
  · simpa using! IsLocalRing.closedPoint_mem_support R N
