/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup

/-!
# Arithmetic subgroups act properly discontinuously
-/

public section

open Matrix

open scoped MatrixGroups UpperHalfPlane

/-
**properlyDiscontinuousSL2ZRange** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：properlyDiscontinuousSL2ZRange : ProperlyDiscontinuousSMul 𝒮ℒ ℍ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.map`：∀ {α β : Type u_1} {s : Set α} (f : α → β), s.Finite → (
f <$> s).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
instance properlyDiscontinuousSL2ZRange : ProperlyDiscontinuousSMul 𝒮ℒ ℍ := by
  let 𝒮ℒ' : Subgroup SL(2, ℝ) := (SpecialLinearGroup.map (Int.castRingHom ℝ)).range
  have : ProperlyDiscontinuousSMul 𝒮ℒ' ℍ := inferInstance
  simp only [Subgroup.properlyDiscontinuousSMul_iff] at this ⊢
  refine fun K L hK hL ↦ ((this hK hL).map SpecialLinearGroup.toGL).subset fun g ↦ ?_
  rintro ⟨⟨γ, rfl⟩, hγ⟩
  exact ⟨γ, ⟨by simp [𝒮ℒ'], hγ⟩, rfl⟩

/-- Arithmetic subgroups of `GL(2, ℝ)` act properly discontinuously on `ℍ`. -/
/-
**Subgroup.IsArithmetic.properlyDiscontinuous** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subgroup.IsArithmetic.properlyDiscontinuous {𝒢 : Subgroup (GL (Fin 2) Real
)} [IsArithmetic 𝒢] : ProperlyDiscontinuousSMul 𝒢 ℍ
参数：GL (Fin 2) Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.Commensurable.properlyDiscontinuousSMul_iff`：Subgroup.Commensur
able.properlyDiscontinuousSMul_iff [MulAction Γ α] [ContinuousConstSMul Γ α] {G 
H : Subgroup Γ} (h : G.Commensurable H) : …
· 使用定理 `Subgroup.IsArithmetic.is_commensurable`：∀ {𝒢 : Subgroup (GL (Fin 2) ℝ)} 
[self : 𝒢.IsArithmetic], 𝒢.Commensurable (Matrix.SpecialLinearGroup.mapGL ℝ).ran
ge

--- 原说明 ---
Arithmetic subgroups of `GL(2, ℝ)` act properly discontinuously on `ℍ`.
-/
instance Subgroup.IsArithmetic.properlyDiscontinuous {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    [IsArithmetic 𝒢] : ProperlyDiscontinuousSMul 𝒢 ℍ := by
  rw [is_commensurable.properlyDiscontinuousSMul_iff]
  infer_instance

end

