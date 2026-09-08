/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Liouville's Theorem for Harmonic Functions on the Complex Plane

A bounded harmonic function on the complex plane is constant.
-/

public section

open Bornology Complex Real Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Auxiliary version of Liouville's theorem, for real-valued harmonic functions on the complex
-- plane.
/-
**InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant_aux** 是 Mathli
b 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant_aux (f : ℂ → ℝ)
    (h_harm : HarmonicOnNhd f univ) (h_bound : Bornology.IsBounded (range f)) :
    ∀ z w, f z = f w := by
  -- By assumption, there exists a holomorphic function $f$ such that $\Re(f) = u$.
  obtain ⟨F, hF_diff, hF_re⟩ := h_harm.exists_analyticOnNhd_univ_re_eq
  -- Since $g(z)$ is bounded, by Liouville's theorem, $g(z)$ is constant.
  suffices ∀ z w, Complex.exp (F z) = Complex.exp (F w) by grind
  apply Differentiable.apply_eq_apply_of_bounded
  · apply (differentiable_exp.comp (fun x ↦ (hF_diff x (mem_univ x)).differentiableAt))
  rw [isBounded_iff_forall_norm_le] at *
  obtain ⟨M, hM⟩ := h_bound
  use Real.exp M
  simp_all only [mem_range, norm_eq_abs, forall_exists_index, forall_apply_eq_imp_iff,
    norm_exp, exp_le_exp]
  rw [← hF_re] at hM
  grind

/--
**Liouville's theorem for harmonic functions on the complex plane** A bounded harmonic function on
the complex plane is constant.
-/
/-
**InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant** 是 Mathlib 中的
一个定理，位于命名空间 ``。
形式化陈述：InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant (f : Compl
ex -> E) (h_harm : HarmonicOnNhd f univ) (h_bound : IsBounded (range f)) : foral
l z w, f z = f w
参数：f : Complex -> E；h_harm : HarmonicOnNhd f univ；h_bound : IsBounded (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `exists_dual_vector''`：exists_dual_vector'' (x : E) : exists g : StrongDu
al 𝕜 E, ‖g‖ <= 1 ∧ g x = ‖x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Bornology.IsBounded.image`：Bornology.IsBounded.image [Bornology α] [Born
ology β] [LocallyBoundedMapClass F α β] (f : F) {s : Set α} (hs : IsBounded s) :
 IsBounded (f '…
· 使用定理 `ContinuousLinearMap.instLocallyBoundedMapClass`：∀ {𝕜 : Type u_1} {𝕜₂ : T
ype u_2} {E : Type u_4} {F : Type u_5} [inst : SeminormedAddCommGroup E]   [inst
_1 : SeminormedAddCommGroup F] [inst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
· 使用定理 `RCLike.ofReal_real_eq_id`：ofReal_real_eq_id : @ofReal Real _ = id
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…

--- 原说明 ---
**Liouville's theorem for harmonic functions on the complex plane** A bounded ha
rmonic function on
the complex plane is constant.
-/
theorem InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant (f : ℂ → E)
    (h_harm : HarmonicOnNhd f univ) (h_bound : IsBounded (range f)) :
    ∀ z w, f z = f w := by
  intro z w
  obtain ⟨ℓ, h₁ℓ, h₂ℓ⟩ := exists_dual_vector'' ℝ (f z - f w)
  rw [map_sub, RCLike.ofReal_real_eq_id, id_eq] at h₂ℓ
  have η₁ : Bornology.IsBounded (range (ℓ ∘ f)) := by
    simpa [range_comp] using IsBounded.image ℓ h_bound
  rw [← sub_eq_zero, ← norm_eq_zero, ← h₂ℓ]
  grind [bounded_harmonic_on_complex_plane_is_constant_aux (ℓ ∘ f) (h_harm.comp_CLM ℓ) η₁]
