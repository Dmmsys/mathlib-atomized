/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Finsupp.Supported

/-! # Results for pointwise instances on `Submodule`s using Finsupp

This file provides the following results in the `Pointwise` locale:

When we consider subsets of `R` acting on `M`
- `Submodule.pointwiseSetDistribMulAction` : the action described above is distributive.
- `Submodule.mem_set_smul` : `x ∈ s • N` iff `x` can be written as `r₀ n₀ + ... + rₖ nₖ` where
  `rᵢ ∈ s` and `nᵢ ∈ N`.
-/

@[expose] public section

assert_not_exists Ideal

variable {α : Type*} {R : Type*} {M : Type*}

open scoped Pointwise

namespace Submodule

variable [Semiring R] [AddCommMonoid M] [Module R M]

section DistribMulAction

variable {S : Type*} [Monoid S]
variable [DistribMulAction S M]

variable (sR : Set R) (s : Set S) (N : Submodule R M)

-- Implementation note: if `N` is both an `R`-submodule and `S`-submodule and `SMulCommClass R S M`,
-- this lemma is also true for any `s : Set S`.
/-
**Submodule.set_smul_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：set_smul_eq_map [SMulCommClass R R N] : sR • N = Submodule.map (N.subtype.
comp (Finsupp.lsum R <| DistribSMul.toLinearMap _ _)) (Finsupp.supported N R sR)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.set_smul_eq_of_le`：set_smul_eq_of_le (p : Submodule R M) (clos
ed_under_smul : forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p) (le : p 
<= s • N) : s • N…
· 使用定理 `Finsupp.single_mem_supported`：single_mem_supported {s : Set α} {a : α} (
b : M) (h : a in s) : single a b in supported M R s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `DistribSMul.toLinearMap_apply`：∀ (R : Type u_1) {S : Type u_3} (M : Type
 u_4) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : Distr…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AddSubmonoid.coe_finsetSum`：∀ {ι : Type u_4} {M : Type u_5} [inst : AddC
ommMonoid M] (S : AddSubmonoid M) (f : ι → ↥S) (s : Finset ι),   ↑(∑ i ∈ s, f i)
 = ∑ i ∈ s, ↑(f …
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用引理 `Submodule.mem_set_smul_def`：mem_set_smul_def (x : M) : x in s • N ↔ x in
 sInf { p : Submodule R M | forall ⦃r : S⦄ {n : M}, r in s -> n in N -> r • n in
 p }
· 使用定理 `Submodule.mem_sInf`：mem_sInf {S : Set (Submodule R M)} {x : M} : x in sI
nf S ↔ forall p in S, x in p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma set_smul_eq_map [SMulCommClass R R N] :
    sR • N =
    Submodule.map
      (N.subtype.comp (Finsupp.lsum R <| DistribSMul.toLinearMap _ _))
      (Finsupp.supported N R sR) := by
  apply set_smul_eq_of_le
  · intro r n hr hn
    exact ⟨Finsupp.single r ⟨n, hn⟩, Finsupp.single_mem_supported _ _ hr, by simp⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := hx
    simp only [LinearMap.coe_comp, coe_subtype, Finsupp.coe_lsum, Finsupp.sum, Function.comp_apply]
    rw [AddSubmonoid.coe_finsetSum]
    refine Submodule.sum_mem (p := sR • N) (t := c.support) ?_ _ ⟨sR • N, ?_⟩
    · rintro r hr
      rw [mem_set_smul_def, Submodule.mem_sInf]
      rintro p hp
      exact hp (hc hr) (c r).2
    · ext x : 1
      simp only [Set.mem_iInter, SetLike.mem_coe]
      fconstructor
      · refine fun h ↦ h fun r n hr hn ↦ ?_
        rw [mem_set_smul_def, mem_sInf]
        exact fun p hp ↦ hp hr hn
      · simp_all
/-
**Submodule.mem_set_smul** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：mem_set_smul (x : M) [SMulCommClass R R N] : x in sR • N ↔ exists (c : R -
>₀ N), (c.support : Set R) subseteq sR ∧ x = c.sum fun r m => r • m
参数：x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.set_smul_eq_map`：set_smul_eq_map [SMulCommClass R R N] : sR • 
N = Submodule.map (N.subtype.comp (Finsupp.lsum R <| DistribSMul.toLinearMap _ _
)) (Finsupp.sup…
· 使用引理 `Submodule.mem_set_smul_def`：mem_set_smul_def (x : M) : x in s • N ↔ x in
 sInf { p : Submodule R M | forall ⦃r : S⦄ {n : M}, r in s -> n in N -> r • n in
 p }
· 使用定理 `Submodule.mem_sInf`：mem_sInf {S : Set (Submodule R M)} {x : M} : x in sI
nf S ↔ forall p in S, x in p
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `AddSubmonoid.coe_finsetSum`：∀ {ι : Type u_4} {M : Type u_5} [inst : AddC
ommMonoid M] (S : AddSubmonoid M) (f : ι → ↥S) (s : Finset ι),   ↑(∑ i ∈ s, f i)
 = ∑ i ∈ s, ↑(f …
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mem_set_smul (x : M) [SMulCommClass R R N] :
    x ∈ sR • N ↔ ∃ (c : R →₀ N), (c.support : Set R) ⊆ sR ∧ x = c.sum fun r m ↦ r • m := by
  fconstructor
  · intro h
    rw [set_smul_eq_map] at h
    obtain ⟨c, hc, rfl⟩ := h
    exact ⟨c, hc, rfl⟩
  · rw [mem_set_smul_def, Submodule.mem_sInf]
    rintro ⟨c, hc1, rfl⟩ p hp
    rw [Finsupp.sum, AddSubmonoid.coe_finsetSum]
    exact Submodule.sum_mem _ fun r hr ↦ hp (hc1 hr) (c _).2

-- Note that this can't be generalized to `Set S`, because even though `SMulCommClass R R M` implies
-- `SMulComm R R N` for all `R`-submodules `N`, `SMulCommClass R S N` for all `R`-submodules `N`
-- does not make sense. If we just focus on `R`-submodules that are also `S`-submodule, then this
-- should be true.
/-- A subset of a ring `R` has a multiplicative action on submodules of a module over `R`. -/
@[instance_reducible]
/-
**Submodule.pointwiseSetMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_2} →   {M : Type u_3} →     [inst : Semiring R] →       [inst_
1 : AddCommMonoid M] →         [inst_2 : _root_.Module R M] → [SMulCommClass R R
 M] → MulAction (Set R) (Submodule R M)
参数：Set R；Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset of a ring `R` has a multiplicative action on submodules of a module ove
r `R`.
-/
protected noncomputable def pointwiseSetMulAction [SMulCommClass R R M] :
    MulAction (Set R) (Submodule R M) where
  one_smul x := show {(1 : R)} • x = x from SetLike.ext fun m =>
    (mem_singleton_set_smul _ _ _).trans ⟨by rintro ⟨_, h, rfl⟩; rwa [one_smul],
      fun h => ⟨m, h, (one_smul _ _).symm⟩⟩
  mul_smul s t x := le_antisymm
    (set_smul_le _ _ _ <| by rintro _ _ ⟨_, _, _, _, rfl⟩ _; rw [mul_smul]; aesop)
    (set_smul_le _ _ _ fun r m hr hm ↦ by
      have : SMulCommClass R R x := ⟨fun r s m => Subtype.ext <| smul_comm _ _ _⟩
      obtain ⟨c, hc1, rfl⟩ := mem_set_smul _ _ _ |>.mp hm
      rw [Finsupp.sum, AddSubmonoid.coe_finsetSum]
      simp only [SetLike.val_smul, Finset.smul_sum, smul_smul]
      exact Submodule.sum_mem _ fun r' hr' ↦
        mem_set_smul_of_mem_mem (Set.mul_mem_mul hr (hc1 hr')) (c _).2)

scoped[Pointwise] attribute [instance] Submodule.pointwiseSetMulAction

-- This cannot be generalized to `Set S` because `MulAction` can't be generalized already.
/-- In a ring, sets acts on submodules. -/
@[instance_reducible]
/-
**Submodule.pointwiseSetDistribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_2} →   {M : Type u_3} →     [inst : Semiring R] →       [inst_
1 : AddCommMonoid M] →         [inst_2 : _root_.Module R M] → [SMulCommClass R R
 M] → DistribMulAction (Set R) (Submodule R M)
参数：Set R；Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a ring, sets acts on submodules.
-/
protected noncomputable def pointwiseSetDistribMulAction [SMulCommClass R R M] :
    DistribMulAction (Set R) (Submodule R M) where
  smul_zero s := set_smul_bot s
  smul_add s x y := le_antisymm
    (set_smul_le _ _ _ <| by
      rintro r m hr hm
      rw [add_eq_sup, Submodule.mem_sup] at hm
      obtain ⟨a, ha, b, hb, rfl⟩ := hm
      rw [smul_add, add_eq_sup, Submodule.mem_sup]
      exact ⟨r • a, mem_set_smul_of_mem_mem (mem1 := hr) (mem2 := ha),
        r • b, mem_set_smul_of_mem_mem (mem1 := hr) (mem2 := hb), rfl⟩)
    (sup_le_iff.mpr ⟨smul_mono_right _ le_sup_left, smul_mono_right _ le_sup_right⟩)

scoped[Pointwise] attribute [instance] Submodule.pointwiseSetDistribMulAction

end DistribMulAction

end Submodule

