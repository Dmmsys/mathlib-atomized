/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Continuity

/-!

# Dimension Shifting

-/

public section

universe v u

variable {R : Type u} [Ring R]

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

open CategoryTheory Abelian

/-- The standard short complex `0 → N → P → M → 0` with `P= R^{⊕M}` free. -/
/-
**ModuleCat.projectiveShortComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ModuleCat.projectiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) : Sho
rtComplex (ModuleCat.{v} R)
参数：M : ModuleCat.{v} R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard short complex `0 → N → P → M → 0` with `P= R^{⊕M}` free.
-/
noncomputable abbrev ModuleCat.projectiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) :
    ShortComplex (ModuleCat.{v} R) :=
  let e : Module.Basis M R (M →₀ Shrink.{v} R) :=
    ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)⟩
  (e.constr ℕ id).shortComplexKer
/-
**ModuleCat.shortExact_projectiveShortComplex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ModuleCat.shortExact_projectiveShortComplex [Small.{v} R] (M : ModuleCat.{
v} R) : M.projectiveShortComplex.ShortExact
参数：M : ModuleCat.{v} R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.shortExact_shortComplexKer`：LinearMap.shortExact_shortComplexK
er {f : M ->ₗ[R] N} (h : Function.Surjective f) : f.shortComplexKer.ShortExact w
here exact
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.constr_apply`：constr_apply (f : ι -> M') (x : M) : constr (
M'
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `Finsupp.mapRange.linearEquiv_apply`：∀ {α : Type u_1} {M : Type u_2} {N :
 Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring
 R₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Shrink.linearEquiv_apply`：∀ (R : Type u_1) (α : Type u_2) [inst : Small.
{v, u_2} α] [inst_1 : Semiring R] [inst_2 : AddCommMonoid α]   [inst_3 : _root_.
Module R α] (a…
· 使用引理 `equivShrink_symm_one`：equivShrink_symm_one [One α] : (equivShrink α).sym
m 1 = 1
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem ModuleCat.shortExact_projectiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) :
    M.projectiveShortComplex.ShortExact := by
  apply LinearMap.shortExact_shortComplexKer
  refine fun m ↦ ⟨Finsupp.single m 1, ?_⟩
  simp [Module.Basis.constr_apply]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{v} R] (M : ModuleCat.{v} R) : Module.Free R M.projectiveShortComplex.X₂ :=
  Module.Free.finsupp R _ _

/-- The connection maps in the contravariant long exact sequence of `Ext` are surjective if
the middle term of the short exact sequence is projective. -/
/-
**precomp_extClass_surjective_of_projective_X** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connection maps in the contravariant long exact sequence of `Ext` are surjec
tive if
the middle term of the short exact sequence is projective.
-/
theorem precomp_extClass_surjective_of_projective_X₂ [Small.{v} R]
    (M : ModuleCat.{v} R) {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (n : ℕ)
    [Projective S.X₂] : Function.Surjective (h.extClass.precomp M (add_comm 1 n)) :=
  fun x ↦ Ext.contravariant_sequence_exact₃ h M x (Ext.eq_zero_of_projective _) (add_comm 1 n)

/-- The connection maps in the covariant long exact sequence of `Ext` are surjective if
the middle term of the short exact sequence is injective. -/
/-
**postcomp_extClass_surjective_of_projective_X** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connection maps in the covariant long exact sequence of `Ext` are surjective
 if
the middle term of the short exact sequence is injective.
-/
theorem postcomp_extClass_surjective_of_projective_X₂ [Small.{v} R]
    {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (M : ModuleCat.{v} R) (n : ℕ)
    [Injective S.X₂] : Function.Surjective (h.extClass.postcomp M (rfl : n + 1 = n + 1)) :=
  fun x ↦ Ext.covariant_sequence_exact₁ M h x (Ext.eq_zero_of_injective _) rfl
