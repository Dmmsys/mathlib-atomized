/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Normed algebra preserves ultrametricity

This file contains the proof that a normed division ring over an ultrametric field is ultrametric.
-/

public section

variable {K L : Type*} [NormedField K]

variable (L) in
/--
The other direction of `IsUltrametricDist.of_normedAlgebra`.
Let `K` be a normed field. If a seminormed ring `L` is a normed `K`-algebra, and `‖1‖ = 1` in `L`,
then `K` is ultrametric (i.e. the norm on `L` is nonarchimedean) if `F` is.
This can be further generalized to the case where `‖1‖ ≠ 0` in `L`.
-/
/-
**IsUltrametricDist.of_normedAlgebra'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUltrametricDist.of_normedAlgebra' [SeminormedRing L] [NormOneClass L] [N
ormedAlgebra K L] [h : IsUltrametricDist L] : IsUltrametricDist K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_algebraMap'`：dist_algebraMap' [NormOneClass 𝕜'] (x y : 𝕜) : (dist (
algebraMap 𝕜 𝕜' x) (algebraMap 𝕜 𝕜' y)) = dist x y
· 使用定理 `IsUltrametricDist.dist_triangle_max`：∀ {X : Type u_2} {inst : Dist X} [s
elf : IsUltrametricDist X] (x y z : X), dist x z ≤ max (dist x y) (dist y z)

--- 原说明 ---
The other direction of `IsUltrametricDist.of_normedAlgebra`.
Let `K` be a normed field. If a seminormed ring `L` is a normed `K`-algebra, and
 `‖1‖ = 1` in `L`,
then `K` is ultrametric (i.e. the norm on `L` is nonarchimedean) if `F` is.
This can be further generalized to the case where `‖1‖ ≠ 0` in `L`.
-/
theorem IsUltrametricDist.of_normedAlgebra' [SeminormedRing L] [NormOneClass L] [NormedAlgebra K L]
    [h : IsUltrametricDist L] : IsUltrametricDist K :=
  ⟨fun x y z => by
    simpa using h.dist_triangle_max (algebraMap K L x) (algebraMap K L y) (algebraMap K L z)⟩

variable (K) in
/--
Let `K` be a normed field. If a normed division ring `L` is a normed `K`-algebra,
then `L` is ultrametric (i.e. the norm on `L` is nonarchimedean) if `K` is.
-/
/-
**IsUltrametricDist.of_normedAlgebra** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUltrametricDist.of_normedAlgebra [NormedDivisionRing L] [NormedAlgebra K
 L] [h : IsUltrametricDist K] : IsUltrametricDist L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isUltrametricDist_iff_forall_norm_natCast_le_one`：isUltrametricDist_iff_
forall_norm_natCast_le_one {R : Type*} [NormedDivisionRing R] : IsUltrametricDis
t R ↔ forall n : Nat, ‖(n : R)‖ <= 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `algebraMap.coe_natCast`：coe_natCast (a : Nat) : (↑(a : R) : A) = a

--- 原说明 ---
Let `K` be a normed field. If a normed division ring `L` is a normed `K`-algebra
,
then `L` is ultrametric (i.e. the norm on `L` is nonarchimedean) if `K` is.
-/
theorem IsUltrametricDist.of_normedAlgebra [NormedDivisionRing L] [NormedAlgebra K L]
    [h : IsUltrametricDist K] : IsUltrametricDist L := by
  rw [isUltrametricDist_iff_forall_norm_natCast_le_one] at h ⊢
  exact fun n => (algebraMap.coe_natCast (R := K) (A := L) n) ▸ norm_algebraMap' L (n : K) ▸ h n

variable (K L) in
/--
Let `K` be a normed field. If a normed division ring `L` is a normed `K`-algebra,
then `L` is ultrametric (i.e. the norm on `L` is nonarchimedean) if and only if `K` is.
-/
/-
**IsUltrametricDist.normedAlgebra_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUltrametricDist.normedAlgebra_iff [NormedDivisionRing L] [NormedAlgebra 
K L] : IsUltrametricDist L ↔ IsUltrametricDist K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUltrametricDist.of_normedAlgebra'`：IsUltrametricDist.of_normedAlgebra'
 [SeminormedRing L] [NormOneClass L] [NormedAlgebra K L] [h : IsUltrametricDist 
L] : IsUltrametricDist K
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `IsUltrametricDist.of_normedAlgebra`：IsUltrametricDist.of_normedAlgebra [
NormedDivisionRing L] [NormedAlgebra K L] [h : IsUltrametricDist K] : IsUltramet
ricDist L

--- 原说明 ---
Let `K` be a normed field. If a normed division ring `L` is a normed `K`-algebra
,
then `L` is ultrametric (i.e. the norm on `L` is nonarchimedean) if and only if 
`K` is.
-/
theorem IsUltrametricDist.normedAlgebra_iff [NormedDivisionRing L] [NormedAlgebra K L] :
    IsUltrametricDist L ↔ IsUltrametricDist K :=
  ⟨fun _ => IsUltrametricDist.of_normedAlgebra' L, fun _ => IsUltrametricDist.of_normedAlgebra K⟩
