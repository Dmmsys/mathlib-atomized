/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.ReesAlgebra

/-!

# `I`-filtrations of modules

This file contains the definitions and basic results around (stable) `I`-filtrations of modules.

## Main results

- `Ideal.Filtration`:
  An `I`-filtration on the module `M` is a sequence of decreasing submodules `N i` such that
  `∀ i, I • (N i) ≤ N (i + 1)`. Note that we do not require the filtration to start from `⊤`.
- `Ideal.Filtration.Stable`: An `I`-filtration is stable if `I • (N i) = N (i + 1)` for large
  enough `i`.
- `Ideal.Filtration.submodule`: The associated module `⨁ Nᵢ` of a filtration, implemented as a
  submodule of `M[X]`.
- `Ideal.Filtration.submodule_fg_iff_stable`: If `F.N i` are all finitely generated, then
  `F.Stable` iff `F.submodule.FG`.
- `Ideal.Filtration.Stable.of_le`: In a finite module over a Noetherian ring,
  if `F' ≤ F`, then `F.Stable → F'.Stable`.
- `Ideal.exists_pow_inf_eq_pow_smul`: **Artin-Rees lemma**.
  given `N ≤ M`, there exists a `k` such that `IⁿM ⊓ N = Iⁿ⁻ᵏ(IᵏM ⊓ N)` for all `n ≥ k`.
- `Ideal.iInf_pow_eq_bot_of_isLocalRing`:
  **Krull's intersection theorem** (`⨅ i, I ^ i = ⊥`) for Noetherian local rings.
- `Ideal.iInf_pow_eq_bot_of_isDomain`:
  **Krull's intersection theorem** (`⨅ i, I ^ i = ⊥`) for Noetherian domains.

-/

@[expose] public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

open Polynomial

open scoped Polynomial

/-- An `I`-filtration on the module `M` is a sequence of decreasing submodules `N i` such that
`I • (N i) ≤ N (i + 1)`. Note that we do not require the filtration to start from `⊤`. -/
@[ext]
/-
**Ideal.Filtration** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ideal`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] → Ideal R → (M : Type u_3) → [inst_
1 : AddCommGroup M] → [_root_.Module R M] → Type u_3
参数：M : Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `I`-filtration on the module `M` is a sequence of decreasing submodules `N i`
 such that
`I • (N i) ≤ N (i + 1)`. Note that we do not require the filtration to start fro
m `⊤`.
-/
structure Ideal.Filtration (M : Type*) [AddCommGroup M] [Module R M] where
  N : ℕ → Submodule R M
  mono : ∀ i, N (i + 1) ≤ N i
  smul_le : ∀ i, I • N i ≤ N (i + 1)

variable (F F' : I.Filtration M) {I}

namespace Ideal.Filtration

/-
**Ideal.Filtration.pow_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtration`。
形式化陈述：pow_smul_le (i j : Nat) : I ^ i • F.N j <= F.N (i + j)
参数：i j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Submodule.top_smul`：top_smul : (⊤ : Ideal R) • N = N
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `smul_mono_right`：smul_mono_right [SMul M α] [Preorder α] [CovariantClass
 M α HSMul.hSMul LE.le] (m : M) : Monotone (HSMul.hSMul m : α -> α)
· 使用定理 `Submodule.instCovariantClassHSMulLe_1`：∀ {R : Type u} [inst : Semiring R
] {A : Type v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A] {M : Type u_1}
   [inst_3 : AddCommMonoid …
· 使用定理 `Ideal.Filtration.smul_le`：∀ {R : Type u_1} [inst : CommRing R] {I : Idea
l R} {M : Type u_3} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (se
lf : I.Filtrat…
-/
theorem pow_smul_le (i j : ℕ) : I ^ i • F.N j ≤ F.N (i + j) := by
  induction i with
  | zero => simp
  | succ _ ih =>
    rw [pow_succ', mul_smul, add_assoc, add_comm 1, ← add_assoc]
    exact (smul_mono_right _ ih).trans (F.smul_le _)
/-
**Ideal.Filtration.pow_smul_le_pow_smul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtrat
ion`。
形式化陈述：pow_smul_le_pow_smul (i j k : Nat) : I ^ (i + k) • F.N j <= I ^ k • F.N (i
 + j)
参数：i j k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `smul_mono_right`：smul_mono_right [SMul M α] [Preorder α] [CovariantClass
 M α HSMul.hSMul LE.le] (m : M) : Monotone (HSMul.hSMul m : α -> α)
· 使用定理 `Submodule.instCovariantClassHSMulLe_1`：∀ {R : Type u} [inst : Semiring R
] {A : Type v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A] {M : Type u_1}
   [inst_3 : AddCommMonoid …
· 使用定理 `Ideal.Filtration.pow_smul_le`：pow_smul_le (i j : Nat) : I ^ i • F.N j <=
 F.N (i + j)
-/
theorem pow_smul_le_pow_smul (i j k : ℕ) : I ^ (i + k) • F.N j ≤ I ^ k • F.N (i + j) := by
  rw [add_comm, pow_add, mul_smul]
  exact smul_mono_right _ (F.pow_smul_le i j)
/-
**Ideal.Filtration.antitone** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtration`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] {I : Ideal R}   (F : I.Filtration M), Antitone 
F.N
参数：F : I.Filtration M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antitone_nat_of_succ_le`：antitone_nat_of_succ_le {f : Nat -> α} (hf : fo
rall n, f (n + 1) <= f n) : Antitone f
· 使用定理 `Ideal.Filtration.mono`：∀ {R : Type u_1} [inst : CommRing R] {I : Ideal R
} {M : Type u_3} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (self 
: I.Filtrat…
-/
protected theorem antitone : Antitone F.N :=
  antitone_nat_of_succ_le F.mono

/-- The trivial `I`-filtration of `N`. -/
@[simps]
/-
**Ideal.Filtration._root_.Ideal.trivialFiltration** 是 Mathlib 中的一个定义，位于命名空间 `Ide
al.Filtration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial `I`-filtration of `N`.
-/
def _root_.Ideal.trivialFiltration (I : Ideal R) (N : Submodule R M) : I.Filtration M where
  N _ := N
  mono _ := le_rfl
  smul_le _ := Submodule.smul_le_right

/-- The `sup` of two `I.Filtration`s is an `I.Filtration`. -/
/-
**Ideal.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Filtration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `sup` of two `I.Filtration`s is an `I.Filtration`.
-/
instance : Max (I.Filtration M) :=
  ⟨fun F F' =>
    ⟨F.N ⊔ F'.N, fun i => sup_le_sup (F.mono i) (F'.mono i), fun i =>
      (Submodule.smul_sup _ _ _).trans_le <| sup_le_sup (F.smul_le i) (F'.smul_le i)⟩⟩

/-- The `sSup` of a family of `I.Filtration`s is an `I.Filtration`. -/
/-
**Ideal.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Filtration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `sSup` of a family of `I.Filtration`s is an `I.Filtration`.
-/
instance : SupSet (I.Filtration M) :=
  ⟨fun S =>
    { N := sSup (Ideal.Filtration.N '' S)
      mono := fun i => by
        apply sSup_le_sSup_of_isCofinalFor _
        rintro _ ⟨⟨_, F, hF, rfl⟩, rfl⟩
        exact ⟨_, ⟨⟨_, F, hF, rfl⟩, rfl⟩, F.mono i⟩
      smul_le := fun i => by
        rw [sSup_eq_iSup', iSup_apply, Submodule.smul_iSup, iSup_apply]
        apply iSup_mono _
        rintro ⟨_, F, hF, rfl⟩
        exact F.smul_le i }⟩

/-- The `inf` of two `I.Filtration`s is an `I.Filtration`. -/
/-
**Ideal.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Filtration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `inf` of two `I.Filtration`s is an `I.Filtration`.
-/
instance : Min (I.Filtration M) :=
  ⟨fun F F' =>
    ⟨F.N ⊓ F'.N, fun i => inf_le_inf (F.mono i) (F'.mono i), fun i =>
      (smul_inf_le _ _ _).trans <| inf_le_inf (F.smul_le i) (F'.smul_le i)⟩⟩

/-- The `sInf` of a family of `I.Filtration`s is an `I.Filtration`. -/
/-
**Ideal.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Filtration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `sInf` of a family of `I.Filtration`s is an `I.Filtration`.
-/
instance : InfSet (I.Filtration M) :=
  ⟨fun S =>
    { N := sInf (Ideal.Filtration.N '' S)
      mono := fun i => by
        apply sInf_le_sInf_of_isCoinitialFor _
        rintro _ ⟨⟨_, F, hF, rfl⟩, rfl⟩
        exact ⟨_, ⟨⟨_, F, hF, rfl⟩, rfl⟩, F.mono i⟩
      smul_le := fun i => by
        rw [sInf_eq_iInf', iInf_apply, iInf_apply]
        refine smul_iInf_le.trans ?_
        apply iInf_mono _
        rintro ⟨_, F, hF, rfl⟩
        exact F.smul_le i }⟩
/-
**Ideal.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Filtration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (I.Filtration M) :=
  ⟨I.trivialFiltration ⊤⟩
/-
**Ideal.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Filtration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (I.Filtration M) :=
  ⟨I.trivialFiltration ⊥⟩

@[simp]
/-
**Ideal.Filtration.sup_N** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtration`。
形式化陈述：sup_N : (F ⊔ F').N = F.N ⊔ F'.N
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_N : (F ⊔ F').N = F.N ⊔ F'.N :=
  rfl

@[simp]
/-
**Ideal.Filtration.sSup_N** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtration`。
形式化陈述：sSup_N (S : Set (I.Filtration M)) : (sSup S).N = sSup (Ideal.Filtration.N 
'' S)
参数：S : Set (I.Filtration M)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sSup_N (S : Set (I.Filtration M)) : (sSup S).N = sSup (Ideal.Filtration.N '' S) :=
  rfl

@[simp]
/-
**Ideal.Filtration.inf_N** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtration`。
形式化陈述：inf_N : (F ⊓ F').N = F.N ⊓ F'.N
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_N : (F ⊓ F').N = F.N ⊓ F'.N :=
  rfl

@[simp]
/-
**Ideal.Filtration.sInf_N** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtration`。
形式化陈述：sInf_N (S : Set (I.Filtration M)) : (sInf S).N = sInf (Ideal.Filtration.N 
'' S)
参数：S : Set (I.Filtration M)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sInf_N (S : Set (I.Filtration M)) : (sInf S).N = sInf (Ideal.Filtration.N '' S) :=
  rfl

@[simp]
/-
**Ideal.Filtration.top_N** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtration`。
形式化陈述：top_N : (⊤ : I.Filtration M).N = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_N : (⊤ : I.Filtration M).N = ⊤ :=
  rfl

@[simp]
/-
**Ideal.Filtration.bot_N** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtration`。
形式化陈述：bot_N : (⊥ : I.Filtration M).N = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_N : (⊥ : I.Filtration M).N = ⊥ :=
  rfl

@[simp]
/-
**Ideal.Filtration.iSup_N** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtration`。
形式化陈述：iSup_N {ι : Sort*} (f : ι -> I.Filtration M) : (iSup f).N = ⨆ i, (f i).N
参数：f : ι -> I.Filtration M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem iSup_N {ι : Sort*} (f : ι → I.Filtration M) : (iSup f).N = ⨆ i, (f i).N :=
  congr_arg sSup (Set.range_comp _ _).symm

@[simp]
/-
**Ideal.Filtration.iInf_N** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtration`。
形式化陈述：iInf_N {ι : Sort*} (f : ι -> I.Filtration M) : (iInf f).N = ⨅ i, (f i).N
参数：f : ι -> I.Filtration M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem iInf_N {ι : Sort*} (f : ι → I.Filtration M) : (iInf f).N = ⨅ i, (f i).N :=
  congr_arg sInf (Set.range_comp _ _).symm
/-
**Ideal.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Filtration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (I.Filtration M) :=
  PartialOrder.lift _ fun _ _ ↦ Ideal.Filtration.ext
/-
**Ideal.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Filtration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (I.Filtration M) :=
  Function.Injective.completeLattice Ideal.Filtration.N
    (fun _ _ ↦ Ideal.Filtration.ext) .rfl .rfl sup_N inf_N
    (fun _ ↦ sSup_image) (fun _ ↦ sInf_image) top_N bot_N
/-
**Ideal.Filtration.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Filtration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (I.Filtration M) :=
  ⟨⊥⟩

/-- An `I` filtration is stable if `I • F.N n = F.N (n+1)` for large enough `n`. -/
/-
**Ideal.Filtration.Stable** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Filtration`。
形式化陈述：Stable : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `I` filtration is stable if `I • F.N n = F.N (n+1)` for large enough `n`.
-/
def Stable : Prop :=
  ∃ n₀, ∀ n ≥ n₀, I • F.N n = F.N (n + 1)

/-- The trivial stable `I`-filtration of `N`. -/
@[simps]
/-
**Ideal.Filtration._root_.Ideal.stableFiltration** 是 Mathlib 中的一个定义，位于命名空间 `Idea
l.Filtration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial stable `I`-filtration of `N`.
-/
def _root_.Ideal.stableFiltration (I : Ideal R) (N : Submodule R M) : I.Filtration M where
  N i := I ^ i • N
  mono i := by rw [add_comm, pow_add, mul_smul]; exact Submodule.smul_le_right
  smul_le i := by rw [add_comm, pow_add, mul_smul, pow_one]

set_option backward.defeqAttrib.useBackward true in
/-
**Ideal.Filtration._root_.Ideal.stableFiltration_stable** 是 Mathlib 中的一个定理，位于命名空
间 `Ideal.Filtration`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ideal.stableFiltration_stable (I : Ideal R) (N : Submodule R M) :
    (I.stableFiltration N).Stable := by
  use 0
  intro n _
  dsimp
  rw [add_comm, pow_add, mul_smul, pow_one]

variable {F F'}
/-
**Ideal.Filtration.Stable.exists_pow_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Fi
ltration.Stable`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] {I : Ideal R}   {F : I.Filtration M}, F.Stable 
→ ∃ n₀, ∀ (k : ℕ), F.N (n₀ + k) = I ^ k • F.N n₀
参数：k : ℕ；n₀ + k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Submodule.top_smul`：top_smul : (⊤ : Ideal R) • N = N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem Stable.exists_pow_smul_eq (h : F.Stable) : ∃ n₀, ∀ k, F.N (n₀ + k) = I ^ k • F.N n₀ := by
  obtain ⟨n₀, hn⟩ := h
  use n₀
  intro k
  induction k with
  | zero => simp
  | succ _ ih => rw [← add_assoc, ← hn, ih, add_comm, pow_add, mul_smul, pow_one]; lia
/-
**Ideal.Filtration.Stable.exists_pow_smul_eq_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Id
eal.Filtration.Stable`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] {I : Ideal R}   {F : I.Filtration M}, F.Stable 
→ ∃ n₀, ∀ n ≥ n₀, F.N n = I ^ (n - n₀) • F.N n₀
参数：n - n₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Filtration.Stable.exists_pow_smul_eq`：∀ {R : Type u_1} {M : Type u
_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {
I : Ideal R}   {F : I.Filtration…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem Stable.exists_pow_smul_eq_of_ge (h : F.Stable) :
    ∃ n₀, ∀ n ≥ n₀, F.N n = I ^ (n - n₀) • F.N n₀ := by
  obtain ⟨n₀, hn₀⟩ := h.exists_pow_smul_eq
  use n₀
  intro n hn
  convert! hn₀ (n - n₀)
  rw [add_comm, tsub_add_cancel_of_le hn]
/-
**Ideal.Filtration.stable_iff_exists_pow_smul_eq_of_ge** 是 Mathlib 中的一个定理，位于命名空间
 `Ideal.Filtration`。
形式化陈述：stable_iff_exists_pow_smul_eq_of_ge : F.Stable ↔ exists n₀, forall n >= n₀
, F.N n = I ^ (n - n₀) • F.N n₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Filtration.Stable.exists_pow_smul_eq_of_ge`：∀ {R : Type u_1} {M : 
Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module 
R M] {I : Ideal R}   {F : I.Filtration…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `tsub_add_eq_add_tsub`：tsub_add_eq_add_tsub (h : b <= a) : a - b + c = a 
+ c - b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
theorem stable_iff_exists_pow_smul_eq_of_ge :
    F.Stable ↔ ∃ n₀, ∀ n ≥ n₀, F.N n = I ^ (n - n₀) • F.N n₀ := by
  refine ⟨Stable.exists_pow_smul_eq_of_ge, fun h => ⟨h.choose, fun n hn => ?_⟩⟩
  rw [h.choose_spec n hn, h.choose_spec (n + 1) (by lia), smul_smul, ← pow_succ',
    tsub_add_eq_add_tsub hn]
/-
**Ideal.Filtration.Stable.exists_forall_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filt
ration.Stable`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] {I : Ideal R}   {F F' : I.Filtration M}, F.Stab
le → F.N 0 ≤ F'.N 0 → ∃ n₀, ∀ (n : ℕ), F.N (n + n₀) ≤ F'.N n
参数：n : ℕ；n + n₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.Filtration.antitone`：∀ {R : Type u_1} {M : Type u_2} [inst : CommR
ing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {I : Ideal R}   (F
 : I.Filtration…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `smul_mono_right`：smul_mono_right [SMul M α] [Preorder α] [CovariantClass
 M α HSMul.hSMul LE.le] (m : M) : Monotone (HSMul.hSMul m : α -> α)
· 使用定理 `Submodule.instCovariantClassHSMulLe_1`：∀ {R : Type u} [inst : Semiring R
] {A : Type v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A] {M : Type u_1}
   [inst_3 : AddCommMonoid …
· 使用定理 `Ideal.Filtration.smul_le`：∀ {R : Type u_1} [inst : CommRing R] {I : Idea
l R} {M : Type u_3} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (se
lf : I.Filtrat…
-/
theorem Stable.exists_forall_le (h : F.Stable) (e : F.N 0 ≤ F'.N 0) :
    ∃ n₀, ∀ n, F.N (n + n₀) ≤ F'.N n := by
  obtain ⟨n₀, hF⟩ := h
  use n₀
  intro n
  induction n with
  | zero => refine (F.antitone ?_).trans e; simp
  | succ n hn =>
    rw [add_right_comm, ← hF]
    · exact (smul_mono_right _ hn).trans (F'.smul_le _)
    simp
/-
**Ideal.Filtration.Stable.bounded_difference** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Fi
ltration.Stable`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] {I : Ideal R}   {F F' : I.Filtration M},   F.St
able → F'.Stable → F.N 0 = F'.N 0 → ∃ n₀, ∀ (n : ℕ), F.N (n + n₀) ≤ F'.N n ∧ F'.
N (n + n₀) ≤ F.N n
参数：n : ℕ；n + n₀；n + n₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Filtration.Stable.exists_forall_le`：∀ {R : Type u_1} {M : Type u_2
} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {I 
: Ideal R}   {F F' : I.Filtrat…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.Filtration.antitone`：∀ {R : Type u_1} {M : Type u_2} [inst : CommR
ing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {I : Ideal R}   (F
 : I.Filtration…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
theorem Stable.bounded_difference (h : F.Stable) (h' : F'.Stable) (e : F.N 0 = F'.N 0) :
    ∃ n₀, ∀ n, F.N (n + n₀) ≤ F'.N n ∧ F'.N (n + n₀) ≤ F.N n := by
  obtain ⟨n₁, h₁⟩ := h.exists_forall_le (le_of_eq e)
  obtain ⟨n₂, h₂⟩ := h'.exists_forall_le (le_of_eq e.symm)
  use max n₁ n₂
  intro n
  refine ⟨(F.antitone ?_).trans (h₁ n), (F'.antitone ?_).trans (h₂ n)⟩ <;> simp

open PolynomialModule

variable (F F')

/-- The `R[IX]`-submodule of `M[X]` associated with an `I`-filtration. -/
/-
**Ideal.Filtration.submodule** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Filtration`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     [inst : CommRing R] →       [inst_
1 : AddCommGroup M] →         [inst_2 : _root_.Module R M] →           {I : Idea
l R} → I.Filtration M → Submodule (↥(reesAlgebra I)) (PolynomialModule R M)
参数：↥(reesAlgebra I)；PolynomialModule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R[IX]`-submodule of `M[X]` associated with an `I`-filtration.
-/
protected noncomputable def submodule : Submodule (reesAlgebra I) (PolynomialModule R M) where
  carrier := { f | ∀ i, f.coeff i ∈ F.N i }
  add_mem' hf hg i := Submodule.add_mem _ (hf i) (hg i)
  zero_mem' _ := Submodule.zero_mem _
  smul_mem' r f hf i := by
    rw [Subalgebra.smul_def, PolynomialModule.smul_apply]
    apply Submodule.sum_mem
    rintro ⟨j, k⟩ e
    rw [Finset.mem_antidiagonal] at e
    subst e
    exact F.pow_smul_le j k (Submodule.smul_mem_smul (r.2 j) (hf k))

@[simp]
/-
**Ideal.Filtration.mem_submodule** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtration`。
形式化陈述：mem_submodule (f : PolynomialModule R M) : f in F.submodule ↔ forall i, f.
coeff i in F.N i
参数：f : PolynomialModule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_submodule (f : PolynomialModule R M) : f ∈ F.submodule ↔ ∀ i, f.coeff i ∈ F.N i :=
  Iff.rfl
/-
**Ideal.Filtration.inf_submodule** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtration`。
形式化陈述：inf_submodule : (F ⊓ F').submodule = F.submodule ⊓ F'.submodule
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
-/
theorem inf_submodule : (F ⊓ F').submodule = F.submodule ⊓ F'.submodule := by
  ext
  exact forall_and

variable (I M)

/-- `Ideal.Filtration.submodule` as an `InfHom`. -/
/-
**Ideal.Filtration.submoduleInfHom** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Filtration`。
形式化陈述：submoduleInfHom : InfHom (I.Filtration M) (Submodule (reesAlgebra I) (Poly
nomialModule R M)) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Filtration.inf_submodule`：inf_submodule : (F ⊓ F').submodule = F.s
ubmodule ⊓ F'.submodule

--- 原说明 ---
`Ideal.Filtration.submodule` as an `InfHom`.
-/
noncomputable def submoduleInfHom :
    InfHom (I.Filtration M) (Submodule (reesAlgebra I) (PolynomialModule R M)) where
  toFun := Ideal.Filtration.submodule
  map_inf' := inf_submodule

variable {I M}
/-
**Ideal.Filtration.submodule_closure_single** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Fil
tration`。
形式化陈述：submodule_closure_single : AddSubmonoid.closure (⋃ i, single R i '' (F.N i
 : Set M)) = F.submodule.toAddSubmonoid
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoid.closure_le`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : S
et M} {S : AddSubmonoid M}, AddSubmonoid.closure s ≤ S ↔ s ⊆ ↑S
· 使用定理 `Set.iUnion_subset_iff`：iUnion_subset_iff {s : ι -> Set α} {t : Set α} : 
⋃ i, s i subseteq t ↔ forall i, s i subseteq t
· 使用定理 `PolynomialModule.coeff_single`：∀ {R : Type u_2} {M : Type u_3} [inst : C
ommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (n : ℕ)   (m :
 M), (PolynomialMod…
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用引理 `PolynomialModule.ofCoeff_coeff`：ofCoeff_coeff (x : PolynomialModule R M)
 : ofCoeff R x.coeff = x
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f
· 使用引理 `PolynomialModule.ofCoeff_finsuppSum`：ofCoeff_finsuppSum [AddCommMonoid N
] (f : ι ->₀ N) (g : ι -> N -> Nat ->₀ M) : ofCoeff R (f.sum g) = f.sum (fun i n
 => ofCoeff R (g i n))
· 使用定理 `AddSubmonoid.sum_mem`：∀ {M : Type u_4} [inst : AddCommMonoid M] (S : Add
Submonoid M) {ι : Type u_5} {t : Finset ι} {f : ι → M},   (∀ c ∈ t, f c ∈ S) → ∑
 c ∈ t, f …
· 使用定理 `AddSubmonoid.subset_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s
 : Set M}, s ⊆ ↑(AddSubmonoid.closure s)
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem submodule_closure_single :
    AddSubmonoid.closure (⋃ i, single R i '' (F.N i : Set M)) = F.submodule.toAddSubmonoid := by
  apply le_antisymm
  · rw [AddSubmonoid.closure_le, Set.iUnion_subset_iff]
    rintro i _ ⟨m, hm, rfl⟩ j
    rw [coeff_single, Finsupp.single_apply]
    split_ifs with h
    · rwa [← h]
    · exact (F.N j).zero_mem
  · intro f hf
    rw [← f.ofCoeff_coeff, ← f.coeff.sum_single, ofCoeff_finsuppSum]
    apply AddSubmonoid.sum_mem _ _
    rintro c -
    exact AddSubmonoid.subset_closure (Set.subset_iUnion _ c <| Set.mem_image_of_mem _ (hf c))
/-
**Ideal.Filtration.submodule_span_single** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtra
tion`。
形式化陈述：submodule_span_single : Submodule.span (reesAlgebra I) (⋃ i, single R i ''
 (F.N i : Set M)) = F.submodule
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_closure`：span_closure {s : Set M} : span R (AddSubmonoid.
closure s : Set M) = span R s
· 使用定理 `Ideal.Filtration.submodule_closure_single`：submodule_closure_single : Ad
dSubmonoid.closure (⋃ i, single R i '' (F.N i : Set M)) = F.submodule.toAddSubmo
noid
· 使用定理 `Submodule.coe_toAddSubmonoid`：coe_toAddSubmonoid (p : Submodule R M) : (
p.toAddSubmonoid : Set M) = p
· 使用定理 `Submodule.span_eq`：span_eq : span R (p : Set M) = p
-/
theorem submodule_span_single :
    Submodule.span (reesAlgebra I) (⋃ i, single R i '' (F.N i : Set M)) = F.submodule := by
  rw [← Submodule.span_closure, submodule_closure_single, Submodule.coe_toAddSubmonoid]
  exact Submodule.span_eq (Filtration.submodule F)

set_option backward.isDefEq.respectTransparency false in
/-
**Ideal.Filtration.submodule_eq_span_le_iff_stable_ge** 是 Mathlib 中的一个定理，位于命名空间 
`Ideal.Filtration`。
形式化陈述：submodule_eq_span_le_iff_stable_ge (n₀ : Nat) : F.submodule = Submodule.sp
an _ (⋃ i <= n₀, single R i '' (F.N i : Set M)) ↔ forall n >= n₀, I • F.N n = F.
N (n + 1)
参数：n₀ : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Filtration.submodule_span_single`：submodule_span_single : Submodul
e.span (reesAlgebra I) (⋃ i, single R i '' (F.N i : Set M)) = F.submodule
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.iUnion₂_subset_iUnion`：iUnion₂_subset_iUnion (κ : ι -> Sort*) (s : ι
 -> Set α) : ⋃ (i) (_ : κ i), s i subseteq ⋃ i, s i
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.iUnion_subset_iff`：iUnion_subset_iff {s : ι -> Set α} {t : Set α} : 
⋃ i, s i subseteq t ↔ forall i, s i subseteq t
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ideal.Filtration.smul_le`：∀ {R : Type u_1} [inst : CommRing R] {I : Idea
l R} {M : Type u_3} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (se
lf : I.Filtrat…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_span_iff_linearCombination`：mem_span_iff_linearCombination (
s : Set M) (x : M) : x in span R s ↔ exists l : s ->₀ R, linearCombination R (↑)
 l = x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `PolynomialModule.coeff_single`：∀ {R : Type u_2} {M : Type u_3} [inst : C
ommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (n : ℕ)   (m :
 M), (PolynomialMod…
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用引理 `PolynomialModule.coeff_finsuppSum`：coeff_finsuppSum [AddCommMonoid N] (f
 : ι ->₀ N) (g : ι -> N -> PolynomialModule R M) : coeff (f.sum g) = f.sum (fun 
i n => coeff (g i n))
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Subalgebra.smul_def`：smul_def [SMul A α] {S : Subalgebra R A} (g : S) (m
 : α) : g • m = (g : A) • m
· 使用定理 `PolynomialModule.smul_single_apply`：smul_single_apply (i : Nat) (f : R[X
]) (m : M) (n : Nat) : (f • single R i m).coeff n = ite (i <= n) (f.coeff (n - i
) • m) 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Filtration.pow_smul_le_pow_smul`：pow_smul_le_pow_smul (i j k : Nat
) : I ^ (i + k) • F.N j <= I ^ k • F.N (i + j)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_tsub_assoc_of_le`：add_tsub_assoc_of_le (h : c <= b) (a : α) : a + b 
- c = a + (b - c)
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
（共 48 条，此处仅展示前 30 条）
-/
theorem submodule_eq_span_le_iff_stable_ge (n₀ : ℕ) :
    F.submodule = Submodule.span _ (⋃ i ≤ n₀, single R i '' (F.N i : Set M)) ↔
      ∀ n ≥ n₀, I • F.N n = F.N (n + 1) := by
  rw [← submodule_span_single,
    ← (Submodule.span_mono (Set.iUnion₂_subset_iUnion _ _)).ge_iff_eq',
    Submodule.span_le, Set.iUnion_subset_iff]
  constructor
  · intro H n hn
    refine (F.smul_le n).antisymm ?_
    intro x hx
    obtain ⟨l, hl⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).mp (H _ ⟨x, hx, rfl⟩)
    replace hl := congr_arg (fun f : PolynomialModule R M => f.coeff (n + 1)) hl
    rw [PolynomialModule.coeff_single, Finsupp.single_apply, if_pos rfl] at hl
    rw [← hl, Finsupp.linearCombination_apply, PolynomialModule.coeff_finsuppSum, Finsupp.sum_apply]
    apply Submodule.sum_mem _ _
    rintro ⟨_, _, ⟨n', rfl⟩, _, ⟨hn', rfl⟩, m, hm, rfl⟩ -
    dsimp only [Subtype.coe_mk]
    rw [Subalgebra.smul_def, smul_single_apply, if_pos (show n' ≤ n + 1 by lia)]
    have e : n' ≤ n := by lia
    have := F.pow_smul_le_pow_smul (n - n') n' 1
    rw [tsub_add_cancel_of_le e, pow_one, add_comm _ 1, ← add_tsub_assoc_of_le e, add_comm] at this
    exact this (Submodule.smul_mem_smul ((l _).2 <| n + 1 - n') hm)
  · let F' := Submodule.span (reesAlgebra I) (⋃ i ≤ n₀, single R i '' (F.N i : Set M))
    intro hF i
    have : ∀ i ≤ n₀, single R i '' (F.N i : Set M) ⊆ F' := fun i hi =>
      -- Porting note: need to add hint for `s`
      (Set.subset_iUnion₂ (s := fun i _ => (single R i '' (N F i : Set M))) i hi).trans
        Submodule.subset_span
    induction i with
    | zero => exact this _ zero_le
    | succ j hj => ?_
    by_cases hj' : j.succ ≤ n₀
    · exact this _ hj'
    simp only [not_le, Nat.lt_succ_iff] at hj'
    rw [← hF _ hj']
    rintro _ ⟨m, hm, rfl⟩
    refine Submodule.smul_induction_on hm (fun r hr m' hm' => ?_) (fun x y hx hy => ?_)
    · rw [add_comm, ← monomial_smul_single]
      exact F'.smul_mem
        ⟨_, reesAlgebra.monomial_mem.mpr (by rwa [pow_one])⟩ (hj <| Set.mem_image_of_mem _ hm')
    · rw [PolynomialModule.single_add]
      exact F'.add_mem hx hy

set_option backward.isDefEq.respectTransparency.types false in
/-- If the components of a filtration are finitely generated, then the filtration is stable iff
its associated submodule of is finitely generated. -/
/-
**Ideal.Filtration.submodule_fg_iff_stable** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filt
ration`。
形式化陈述：submodule_fg_iff_stable (hF' : forall i, (F.N i).FG) : F.submodule.FG ↔ F.
Stable
参数：hF' : forall i, (F.N i).FG。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Filtration.submodule_eq_span_le_iff_stable_ge`：submodule_eq_span_l
e_iff_stable_ge (n₀ : Nat) : F.submodule = Submodule.span _ (⋃ i <= n₀, single R
 i '' (F.N i : Set M)) ↔ forall n >= n₀, …
· 使用定理 `Submodule.FG.stabilizes_of_iSup_eq`：∀ {R : Type u_1} {M : Type u_2} [ins
t : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {M' : 
Submodule R M}, M'.FG → …
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.iUnion₂_subset_iff`：iUnion₂_subset_iff {s : forall i, κ i -> Set α} 
{t : Set α} : ⋃ (i) (j), s i j subseteq t ↔ forall i j, s i j subseteq t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.subset_iUnion₂`：subset_iUnion₂ {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : s i j subseteq ⋃ (i') (j'), s i' j'
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Submodule.span_iUnion`：span_iUnion {ι} (s : ι -> Set M) : span R (⋃ i, s
 i) = ⨆ i, span R (s i)
· 使用定理 `Ideal.Filtration.submodule_span_single`：submodule_span_single : Submodul
e.span (reesAlgebra I) (⋃ i, single R i '' (F.N i : Set M)) = F.submodule
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.biUnion_le_eq_iUnion`：biUnion_le_eq_iUnion [Preorder α] {s : α -> Se
t β} : ⋃ (n) (m <= n), s m = ⋃ n, s n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.span_iUnion₂`：span_iUnion₂ {ι} {κ : ι -> Sort*} (s : forall i,
 κ i -> Set M) : span R (⋃ (i) (j), s i j) = ⨆ (i) (j), span R (s i j)
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `Submodule.fg_iSup`：fg_iSup {ι : Sort*} [Finite ι] (N : ι -> Submodule R 
M) (h : forall i, (N i).FG) : (iSup N).FG
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s
· 使用定理 `Subalgebra.isScalarTower_mid`：∀ {R : Type u} {A : Type v} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {α
 : Type u_1} {β : …
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a

--- 原说明 ---
If the components of a filtration are finitely generated, then the filtration is
 stable iff
its associated submodule of is finitely generated.
-/
theorem submodule_fg_iff_stable (hF' : ∀ i, (F.N i).FG) : F.submodule.FG ↔ F.Stable := by
  classical
  delta Ideal.Filtration.Stable
  simp_rw [← F.submodule_eq_span_le_iff_stable_ge]
  constructor
  · rintro H
    refine H.stabilizes_of_iSup_eq
        ⟨fun n₀ => Submodule.span _ (⋃ (i : ℕ) (_ : i ≤ n₀), single R i '' ↑(F.N i)), ?_⟩ ?_
    · intro n m e
      rw [Submodule.span_le, Set.iUnion₂_subset_iff]
      intro i hi
      refine Set.Subset.trans ?_ Submodule.subset_span
      refine @Set.subset_iUnion₂ _ _ _ (fun i => fun _ => ↑((single R i) '' ((N F i) : Set M))) i ?_
      exact hi.trans e
    · dsimp
      rw [← Submodule.span_iUnion, ← submodule_span_single]
      simp [Set.biUnion_le_eq_iUnion]
  · rintro ⟨n, hn⟩
    rw [hn]
    simp_rw [Submodule.span_iUnion₂, ← Finset.mem_range_succ_iff, iSup_subtype']
    apply Submodule.fg_iSup
    rintro ⟨i, hi⟩
    obtain ⟨s, hs⟩ := hF' i
    have : Submodule.span (reesAlgebra I) (s.image (lsingle R i) : Set (PolynomialModule R M)) =
        Submodule.span _ (single R i '' (F.N i : Set M)) := by
      rw [Finset.coe_image, ← Submodule.span_span_of_tower R, ← Submodule.map_span, hs]; rfl
    rw [Subtype.coe_mk, ← this]
    exact ⟨_, rfl⟩

variable {F}
/-
**Ideal.Filtration.Stable.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtration.Stab
le`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] {I : Ideal R}   {F : I.Filtration M} [IsNoether
ianRing R] [Module.Finite R M], F.Stable → ∀ {F' : I.Filtration M}, F' ≤ F → F'.
Stable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Filtration.submodule_fg_iff_stable`：submodule_fg_iff_stable (hF' :
 forall i, (F.N i).FG) : F.submodule.FG ↔ F.Stable
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `isNoetherian_of_fg_of_noetherian`：isNoetherian_of_fg_of_noetherian {R M}
 [Ring R] [AddCommGroup M] [Module R M] (N : Submodule R M) [I : IsNoetherianRin
g R] (hN : N.FG) : IsN…
· 使用定理 `instIsNoetherianRingSubtypePolynomialMemSubalgebraReesAlgebra`：∀ {R : Ty
pe u} [inst : CommRing R] {I : Ideal R} [IsNoetherianRing R], IsNoetherianRing ↥
(reesAlgebra I)
· 使用定理 `isNoetherian_submodule`：isNoetherian_submodule {N : Submodule R M} : IsN
oetherian R N ↔ forall s : Submodule R M, s <= N -> s.FG
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `InfHomClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : FunLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : SemilatticeIn
f β] [InfHomClass…
· 使用定理 `InfHom.instInfHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Min α] [
inst_1 : Min β], InfHomClass (InfHom α β) α β
-/
theorem Stable.of_le [IsNoetherianRing R] [Module.Finite R M] (hF : F.Stable)
    {F' : I.Filtration M} (hf : F' ≤ F) : F'.Stable := by
  rw [← submodule_fg_iff_stable] at hF ⊢
  any_goals intro i; exact IsNoetherian.noetherian _
  have := isNoetherian_of_fg_of_noetherian _ hF
  rw [isNoetherian_submodule] at this
  exact this _ (OrderHomClass.mono (submoduleInfHom M I) hf)
/-
**Ideal.Filtration.Stable.inter_right** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtratio
n.Stable`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] {I : Ideal R}   {F : I.Filtration M} (F' : I.Fi
ltration M) [IsNoetherianRing R] [Module.Finite R M], F.Stable → (F ⊓ F').Stable
参数：F' : I.Filtration M；F ⊓ F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Filtration.Stable.of_le`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {I : Ideal R} 
  {F : I.Filtration…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem Stable.inter_right [IsNoetherianRing R] [Module.Finite R M] (hF : F.Stable) :
    (F ⊓ F').Stable :=
  hF.of_le inf_le_left
/-
**Ideal.Filtration.Stable.inter_left** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Filtration
.Stable`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] {I : Ideal R}   {F : I.Filtration M} (F' : I.Fi
ltration M) [IsNoetherianRing R] [Module.Finite R M], F.Stable → (F' ⊓ F).Stable
参数：F' : I.Filtration M；F' ⊓ F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Filtration.Stable.of_le`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {I : Ideal R} 
  {F : I.Filtration…
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem Stable.inter_left [IsNoetherianRing R] [Module.Finite R M] (hF : F.Stable) :
    (F' ⊓ F).Stable :=
  hF.of_le inf_le_right

end Ideal.Filtration

variable (I)

/-- **Artin-Rees lemma** -/
/-
**Ideal.exists_pow_inf_eq_pow_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.exists_pow_inf_eq_pow_smul [IsNoetherianRing R] [Module.Finite R M] 
(N : Submodule R M) : exists k : Nat, forall n >= k, I ^ n • ⊤ ⊓ N = I ^ (n - k)
 • (I ^ k • ⊤ ⊓ N)
参数：N : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Filtration.Stable.exists_pow_smul_eq_of_ge`：∀ {R : Type u_1} {M : 
Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module 
R M] {I : Ideal R}   {F : I.Filtration…
· 使用定理 `Ideal.Filtration.Stable.inter_right`：∀ {R : Type u_1} {M : Type u_2} [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {I : Ide
al R}   {F : I.Filtration…
· 使用定理 `Ideal.stableFiltration_stable`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (I : Ideal R) 
  (N : Submodule R …

--- 原说明 ---
**Artin-Rees lemma**
-/
theorem Ideal.exists_pow_inf_eq_pow_smul [IsNoetherianRing R] [Module.Finite R M]
    (N : Submodule R M) : ∃ k : ℕ, ∀ n ≥ k, I ^ n • ⊤ ⊓ N = I ^ (n - k) • (I ^ k • ⊤ ⊓ N) :=
  ((I.stableFiltration_stable ⊤).inter_right (I.trivialFiltration N)).exists_pow_smul_eq_of_ge
/-
**Ideal.mem_iInf_smul_pow_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.mem_iInf_smul_pow_eq_bot_iff [IsNoetherianRing R] [Module.Finite R M
] (x : M) : x in (⨅ i : Nat, I ^ i • ⊤ : Submodule R M) ↔ exists r : I, (r : R) 
• x = x
参数：x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.stableFiltration_N`：∀ {R : Type u_1} {M : Type u_2} [inst : CommRi
ng R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (I : Ideal R)   (N 
: Submodule R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul`：exists_mem_and_s
mul_eq_self_of_fg_of_le_smul {R : Type*} [CommRing R] {M : Type*} [AddCommGroup 
M] [Module R M] (I : Ideal R) (N : Submodule…
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `Ideal.Filtration.Stable.inter_right`：∀ {R : Type u_1} {M : Type u_2} [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {I : Ide
al R}   {F : I.Filtration…
· 使用定理 `Ideal.stableFiltration_stable`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (I : Ideal R) 
  (N : Submodule R …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_iInf`：mem_iInf {ι} (p : ι -> Submodule R M) {x} : x in ⨅ i
, p i ↔ forall i, x in p i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Submodule.top_smul`：top_smul : (⊤ : Ideal R) • N = N
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem Ideal.mem_iInf_smul_pow_eq_bot_iff [IsNoetherianRing R] [Module.Finite R M] (x : M) :
    x ∈ (⨅ i : ℕ, I ^ i • ⊤ : Submodule R M) ↔ ∃ r : I, (r : R) • x = x := by
  let N := (⨅ i : ℕ, I ^ i • ⊤ : Submodule R M)
  have hN : ∀ k, (I.stableFiltration ⊤ ⊓ I.trivialFiltration N).N k = N :=
    fun k => inf_eq_right.mpr ((iInf_le _ k).trans <| le_of_eq <| by simp)
  constructor
  · obtain ⟨r, hr₁, hr₂⟩ :=
      Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I N (IsNoetherian.noetherian N) (by
        obtain ⟨k, hk⟩ := (I.stableFiltration_stable ⊤).inter_right (I.trivialFiltration N)
        have := hk k (le_refl _)
        rw [hN, hN] at this
        exact le_of_eq this.symm)
    intro H
    exact ⟨⟨r, hr₁⟩, hr₂ _ H⟩
  · rintro ⟨r, eq⟩
    rw [Submodule.mem_iInf]
    intro i
    induction i with
    | zero => simp
    | succ i hi =>
      rw [add_comm, pow_add, ← smul_smul, pow_one, ← eq]
      exact Submodule.smul_mem_smul r.prop hi
/-
**Ideal.iInf_pow_smul_eq_bot_of_le_jacobson** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.iInf_pow_smul_eq_bot_of_le_jacobson [IsNoetherianRing R] [Module.Fin
ite R M] (h : I <= Ideal.jacobson ⊥) : (⨅ i : Nat, I ^ i • ⊤ : Submodule R M) = 
⊥
参数：h : I <= Ideal.jacobson ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_iInf_smul_pow_eq_bot_iff`：Ideal.mem_iInf_smul_pow_eq_bot_iff [
IsNoetherianRing R] [Module.Finite R M] (x : M) : x in (⨅ i : Nat, I ^ i • ⊤ : S
ubmodule R M) ↔ exists r…
· 使用定理 `Ideal.isUnit_of_sub_one_mem_jacobson_bot`：isUnit_of_sub_one_mem_jacobson
_bot (r : R) (h : r - 1 in jacobson (⊥ : Ideal R)) : IsUnit r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - b - a = -b
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
· 使用定理 `instNonUnitalSubringClassIdeal`：∀ {R : Type u_1} [inst : Ring R], NonUni
talSubringClass (Ideal R) R
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `IsUnit.smul_left_cancel`：smul_left_cancel {a : α} (ha : IsUnit a) {x y :
 β} : a • x = a • y ↔ x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ideal.iInf_pow_smul_eq_bot_of_le_jacobson [IsNoetherianRing R]
    [Module.Finite R M] (h : I ≤ Ideal.jacobson ⊥) : (⨅ i : ℕ, I ^ i • ⊤ : Submodule R M) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨r, hr⟩ := (I.mem_iInf_smul_pow_eq_bot_iff x).mp hx
  have := isUnit_of_sub_one_mem_jacobson_bot (1 - r.1) (by simpa using h r.2)
  apply this.smul_left_cancel.mp
  simp [sub_smul, hr]

open IsLocalRing in
/-
**Ideal.iInf_pow_smul_eq_bot_of_isLocalRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.iInf_pow_smul_eq_bot_of_isLocalRing [IsNoetherianRing R] [IsLocalRin
g R] [Module.Finite R M] (h : I != ⊤) : (⨅ i : Nat, I ^ i • ⊤ : Submodule R M) =
 ⊥
参数：h : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`：Ideal.iInf_pow_smul_eq_bot_of
_le_jacobson [IsNoetherianRing R] [Module.Finite R M] (h : I <= Ideal.jacobson ⊥
) : (⨅ i : Nat, I ^ i • ⊤ : Sub…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsLocalRing.le_maximalIdeal`：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤)
 : J <= maximalIdeal R
· 使用定理 `IsLocalRing.maximalIdeal_le_jacobson`：maximalIdeal_le_jacobson (I : Idea
l R) : IsLocalRing.maximalIdeal R <= I.jacobson
-/
theorem Ideal.iInf_pow_smul_eq_bot_of_isLocalRing [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] (h : I ≠ ⊤) : (⨅ i : ℕ, I ^ i • ⊤ : Submodule R M) = ⊥ :=
  Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _
    ((le_maximalIdeal h).trans (maximalIdeal_le_jacobson _))

/-- **Krull's intersection theorem** for Noetherian local rings. -/
/-
**Ideal.iInf_pow_eq_bot_of_isLocalRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.iInf_pow_eq_bot_of_isLocalRing [IsNoetherianRing R] [IsLocalRing R] 
(h : I != ⊤) : ⨅ i : Nat, I ^ i = ⊥
参数：h : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`：Ideal.iInf_pow_smul_eq_bot_of
_isLocalRing [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M] (h : I != 
⊤) : (⨅ i : Nat, I ^ i • ⊤ : Su…

--- 原说明 ---
**Krull's intersection theorem** for Noetherian local rings.
-/
theorem Ideal.iInf_pow_eq_bot_of_isLocalRing [IsNoetherianRing R] [IsLocalRing R] (h : I ≠ ⊤) :
    ⨅ i : ℕ, I ^ i = ⊥ := by
  convert! I.iInf_pow_smul_eq_bot_of_isLocalRing (M := R) h
  ext i
  rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one]

/-- Also see `Ideal.isIdempotentElem_iff_eq_bot_or_top` for integral domains. -/
/-
**Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing {R} [CommRing R] [
IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) : IsIdempotentElem I ↔ I = ⊥ ∨
 I = ⊤
参数：I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.iInf_pow_eq_bot_of_isLocalRing`：Ideal.iInf_pow_eq_bot_of_isLocalRi
ng [IsNoetherianRing R] [IsLocalRing R] (h : I != ⊤) : ⨅ i : Nat, I ^ i = ⊥
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用引理 `IsIdempotentElem.pow_succ_eq`：pow_succ_eq (n : Nat) (h : IsIdempotentEle
m a) : a ^ (n + 1) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.mul_bot`：mul_bot : M * ⊥ = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
Also see `Ideal.isIdempotentElem_iff_eq_bot_or_top` for integral domains.
-/
theorem Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing {R} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) :
    IsIdempotentElem I ↔ I = ⊥ ∨ I = ⊤ := by
  constructor
  · intro H
    by_cases I = ⊤; · exact Or.inr ‹_›
    refine Or.inl (eq_bot_iff.mpr ?_)
    rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing I ‹_›]
    apply le_iInf
    rintro (_ | n) <;> simp [H.pow_succ_eq]
  · rintro (rfl | rfl) <;> simp [IsIdempotentElem]

open IsLocalRing in
/-
**Ideal.iInf_pow_smul_eq_bot_of_isTorsionFree** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.iInf_pow_smul_eq_bot_of_isTorsionFree [IsDomain R] [IsNoetherianRing
 R] [Module.IsTorsionFree R M] [Module.Finite R M] (h : I != ⊤) : (⨅ i : Nat, I 
^ i • ⊤ : Submodule R M) = ⊥
参数：h : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ideal.mem_iInf_smul_pow_eq_bot_iff`：Ideal.mem_iInf_smul_pow_eq_bot_iff [
IsNoetherianRing R] [Module.Finite R M] (x : M) : x in (⨅ i : Nat, I ^ i • ⊤ : S
ubmodule R M) ↔ exists r…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem Ideal.iInf_pow_smul_eq_bot_of_isTorsionFree [IsDomain R]
    [IsNoetherianRing R] [Module.IsTorsionFree R M]
    [Module.Finite R M] (h : I ≠ ⊤) : (⨅ i : ℕ, I ^ i • ⊤ : Submodule R M) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  by_contra hx'
  have := Ideal.mem_iInf_smul_pow_eq_bot_iff I x
  obtain ⟨r, hr⟩ := this.mp hx
  have := smul_left_injective _ hx' (hr.trans (one_smul _ x).symm)
  exact I.eq_top_iff_one.not.mp h (this ▸ r.prop)

@[deprecated (since := "2026-01-17")]
alias Ideal.iInf_pow_smul_eq_bot_of_noZeroSMulDivisors :=
  Ideal.iInf_pow_smul_eq_bot_of_isTorsionFree

/-- **Krull's intersection theorem** for Noetherian domains. -/
/-
**Ideal.iInf_pow_eq_bot_of_isDomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.iInf_pow_eq_bot_of_isDomain [IsNoetherianRing R] [IsDomain R] (h : I
 != ⊤) : ⨅ i : Nat, I ^ i = ⊥
参数：h : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.iInf_pow_smul_eq_bot_of_isTorsionFree`：Ideal.iInf_pow_smul_eq_bot_
of_isTorsionFree [IsDomain R] [IsNoetherianRing R] [Module.IsTorsionFree R M] [M
odule.Finite R M] (h : I != ⊤) : …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α

--- 原说明 ---
**Krull's intersection theorem** for Noetherian domains.
-/
theorem Ideal.iInf_pow_eq_bot_of_isDomain [IsNoetherianRing R] [IsDomain R] (h : I ≠ ⊤) :
    ⨅ i : ℕ, I ^ i = ⊥ := by
  convert! I.iInf_pow_smul_eq_bot_of_isTorsionFree (M := R) h
  simp
