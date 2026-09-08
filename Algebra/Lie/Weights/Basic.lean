/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Ring.Divisibility.Lemmas
public import Mathlib.Algebra.Lie.Nilpotent
public import Mathlib.Algebra.Lie.Engel
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Weight spaces of Lie modules of nilpotent Lie algebras

Just as a key tool when studying the behaviour of a linear operator is to decompose the space on
which it acts into a sum of (generalised) eigenspaces, a key tool when studying a representation `M`
of Lie algebra `L` is to decompose `M` into a sum of simultaneous eigenspaces of `x` as `x` ranges
over `L`. These simultaneous generalised eigenspaces are known as the weight spaces of `M`.

When `L` is nilpotent, it follows from the binomial theorem that weight spaces are Lie submodules.

Basic definitions and properties of the above ideas are provided in this file.

## Main definitions

  * `LieModule.genWeightSpaceOf`
  * `LieModule.genWeightSpace`
  * `LieModule.Weight`
  * `LieModule.posFittingCompOf`
  * `LieModule.posFittingComp`
  * `LieModule.iSup_ucs_eq_genWeightSpace_zero`
  * `LieModule.iInf_lowerCentralSeries_eq_posFittingComp`
  * `LieModule.isCompl_genWeightSpace_zero_posFittingComp`
  * `LieModule.iSupIndep_genWeightSpace`
  * `LieModule.iSup_genWeightSpace_eq_top`

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 7--9*](bourbaki1975b)

## Tags

lie character, eigenvalue, eigenspace, weight, weight vector, root, root vector
-/

@[expose] public section

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

open Set Function TensorProduct LieModule

variable (M) in
/-- If `M` is a representation of a Lie algebra `L` and `χ : L → R` is a family of scalars,
then `weightSpace M χ` is the intersection of the `χ x`-eigenspaces
of the action of `x` on `M` as `x` ranges over `L`. -/
/-
**LieModule.weightSpace** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：weightSpace (χ : L -> R) : LieSubmodule R L M where __
参数：χ : L -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is a representation of a Lie algebra `L` and `χ : L → R` is a family of s
calars,
then `weightSpace M χ` is the intersection of the `χ x`-eigenspaces
of the action of `x` on `M` as `x` ranges over `L`.
-/
def weightSpace (χ : L → R) : LieSubmodule R L M where
  __ := ⨅ x : L, (toEnd R L M x).eigenspace (χ x)
  lie_mem {x m} hm := by simp_all [smul_comm (χ x)]
/-
**LieModule.mem_weightSpace** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：mem_weightSpace (χ : L -> R) (m : M) : m in weightSpace M χ ↔ forall x, ⁅x
, m⁆ = χ x • m
参数：χ : L -> R；m : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_weightSpace (χ : L → R) (m : M) : m ∈ weightSpace M χ ↔ ∀ x, ⁅x, m⁆ = χ x • m := by
  simp [weightSpace]

section notation_genWeightSpaceOf

/-- Until we define `LieModule.genWeightSpaceOf`, it is useful to have some notation as follows: -/
local notation3 "𝕎("M", " χ", " x")" => (toEnd R L M x).maxGenEigenspace χ

/-- See also `bourbaki1975b` Chapter VII §1.1, Proposition 2 (ii). -/
/-
**LieModule.weight_vector_multiplication** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ {R : Type u_2} {L : Type u_3} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] (M₁ : Type u_5)   (M₂ : Type u_6) (M₃ : Type u_7) [inst
_3 : AddCommGroup M₁] [inst_4 : _root_.Module R M₁] [inst_5 : LieRingModule L M₁
]   [inst_6 : LieModule R L M₁] [inst_7 : AddCommGroup M₂] [inst_8 : _root_.Modu
le R M₂] [inst_9 : LieRingModule L M₂]   [inst_10 : LieModule R L M₂] [inst_11 :
 AddCommGroup M₃] [inst_12 : _root_.Module R M₃] [inst_13 : LieRingModule L M₃] 
  [inst_14 : LieModule R L M₃] (g : TensorProduct R M₁ M₂ →ₗ⁅R,L⁆ M₃) (χ₁ χ₂ : R
) (x : L),   (↑g ∘ₗ         TensorProduct.mapIncl (((LieModule.toEnd R L M₁) x).
maxGenEigenspace χ₁)           (((LieModule.toEnd R L M₂) x).maxGenEigenspace χ₂
)).range ≤     ((LieModule.toEnd R L M₃) x).maxGenEigenspace (χ₁ + χ₂)
参数：M₁ : Type u_5；M₂ : Type u_6；M₃ : Type u_7；g : TensorProduct R M₁ M₂ →ₗ⁅R,L⁆ M
₃；χ₁ χ₂ : R；x : L；↑g ∘ₗ         TensorProduct.mapIncl (((LieModule.toEnd R L M₁)
 x).maxGenEigenspace χ₁)           (((LieModule.toEnd R L M₂) x).maxGenEigenspac
e χ₂)；(LieModule.toEnd R L M₃) x；χ₁ + χ₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `LieModuleHom.instLinearMapClass`：∀ {R : Type u} {L : Type v} {M : Type w
} {N : Type w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGrou
p M] [inst_3 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModuleHom.map_lie`：map_lie (f : M ->ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x,
 m⁆ = ⁅x, f m⁆
· 使用定理 `TensorProduct.LieModule.lie_tmul_right`：lie_tmul_right (x : L) (m : M) (
n : N) : ⁅x, m otimesₜ[R] n⁆ = ⁅x, m⁆ otimesₜ n + m otimesₜ ⁅x, n⁆
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `TensorProduct.sub_tmul`：sub_tmul (m₁ m₂ : M) (n : N) : (m₁ - m₂) otimesₜ
 n = m₁ otimesₜ[R] n - m₂ otimesₜ[R] n
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.tmul_sub`：tmul_sub (m : M) (p₁ p₂ : P) : m otimesₜ (p₁ - p
₂) = m otimesₜ[R] p₁ - m otimesₜ[R] p₂
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
See also `bourbaki1975b` Chapter VII §1.1, Proposition 2 (ii).
-/
protected theorem weight_vector_multiplication (M₁ M₂ M₃ : Type*)
    [AddCommGroup M₁] [Module R M₁] [LieRingModule L M₁] [LieModule R L M₁] [AddCommGroup M₂]
    [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂] [AddCommGroup M₃] [Module R M₃]
    [LieRingModule L M₃] [LieModule R L M₃] (g : M₁ ⊗[R] M₂ →ₗ⁅R,L⁆ M₃) (χ₁ χ₂ : R) (x : L) :
    LinearMap.range ((g : M₁ ⊗[R] M₂ →ₗ[R] M₃).comp (mapIncl 𝕎(M₁, χ₁, x) 𝕎(M₂, χ₂, x))) ≤
      𝕎(M₃, χ₁ + χ₂, x) := by
  -- Unpack the statement of the goal.
  intro m₃
  simp only [TensorProduct.mapIncl, LinearMap.mem_range, LinearMap.coe_comp,
    LieModuleHom.coe_toLinearMap, Function.comp_apply, exists_imp, Module.End.mem_maxGenEigenspace]
  rintro t rfl
  -- Set up some notation.
  let F : Module.End R M₃ := toEnd R L M₃ x - (χ₁ + χ₂) • ↑1
  -- The goal is linear in `t` so use induction to reduce to the case that `t` is a pure tensor.
  refine t.induction_on ?_ ?_ ?_
  · use 0; simp only [map_zero]
  swap
  · rintro t₁ t₂ ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩; use max k₁ k₂
    simp only [map_add, Module.End.pow_map_zero_of_le (le_max_left k₁ k₂) hk₁,
      Module.End.pow_map_zero_of_le (le_max_right k₁ k₂) hk₂, add_zero]
  -- Now the main argument: pure tensors.
  rintro ⟨m₁, hm₁⟩ ⟨m₂, hm₂⟩
  change ∃ k, (F ^ k) ((g : M₁ ⊗[R] M₂ →ₗ[R] M₃) (m₁ ⊗ₜ m₂)) = (0 : M₃)
  -- Eliminate `g` from the picture.
  let f₁ : Module.End R (M₁ ⊗[R] M₂) := (toEnd R L M₁ x - χ₁ • ↑1).rTensor M₂
  let f₂ : Module.End R (M₁ ⊗[R] M₂) := (toEnd R L M₂ x - χ₂ • ↑1).lTensor M₁
  have h_comm_square : F ∘ₗ ↑g = (g : M₁ ⊗[R] M₂ →ₗ[R] M₃).comp (f₁ + f₂) := by
    ext m₁ m₂
    simp only [f₁, f₂, F, ← g.map_lie x (m₁ ⊗ₜ m₂), add_smul, sub_tmul, tmul_sub, smul_tmul,
      lie_tmul_right, tmul_smul, toEnd_apply_apply, map_smul, Module.End.one_apply,
      LieModuleHom.coe_toLinearMap, LinearMap.smul_apply, Function.comp_apply, LinearMap.coe_comp,
      LinearMap.rTensor_tmul, map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply,
      LinearMap.lTensor_tmul, AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars]
    abel
  rsuffices ⟨k, hk⟩ : ∃ k : ℕ, ((f₁ + f₂) ^ k) (m₁ ⊗ₜ m₂) = 0
  · use k
    rw [← LinearMap.comp_apply, Module.End.commute_pow_left_of_commute h_comm_square,
      LinearMap.comp_apply, hk, map_zero]
  -- Unpack the information we have about `m₁`, `m₂`.
  simp only [Module.End.mem_maxGenEigenspace] at hm₁ hm₂
  obtain ⟨k₁, hk₁⟩ := hm₁
  obtain ⟨k₂, hk₂⟩ := hm₂
  have hf₁ : (f₁ ^ k₁) (m₁ ⊗ₜ m₂) = 0 := by
    simp only [f₁, hk₁, zero_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_pow]
  have hf₂ : (f₂ ^ k₂) (m₁ ⊗ₜ m₂) = 0 := by
    simp only [f₂, hk₂, tmul_zero, LinearMap.lTensor_tmul, LinearMap.lTensor_pow]
  -- It's now just an application of the binomial theorem.
  use k₁ + k₂ - 1
  have hf_comm : Commute f₁ f₂ := by
    ext m₁ m₂
    simp only [f₁, f₂, Module.End.mul_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      AlgebraTensorModule.curry_apply, LinearMap.lTensor_tmul, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars]
  rw [hf_comm.add_pow']
  simp only [Finset.sum_apply, LinearMap.coe_sum, LinearMap.smul_apply]
  -- The required sum is zero because each individual term is zero.
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  -- Eliminate the binomial coefficients from the picture.
  suffices (f₁ ^ i * f₂ ^ j) (m₁ ⊗ₜ m₂) = 0 by rw [this]; apply smul_zero
  -- Finish off with appropriate case analysis.
  rcases Nat.le_or_le_of_add_eq_add_pred (Finset.mem_antidiagonal.mp hij) with hi | hj
  · rw [(hf_comm.pow_pow i j).eq, Module.End.mul_apply, Module.End.pow_map_zero_of_le hi hf₁,
      map_zero]
  · rw [Module.End.mul_apply, Module.End.pow_map_zero_of_le hj hf₂, map_zero]
/-
**LieModule.lie_mem_maxGenEigenspace_toEnd** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`
。
形式化陈述：lie_mem_maxGenEigenspace_toEnd {χ₁ χ₂ : R} {x y : L} {m : M} (hy : y in 𝕎(
L, χ₁, x)) (hm : m in 𝕎(M, χ₂, x)) : ⁅y, m⁆ in 𝕎(M, χ₁ + χ₂, x)
参数：hy : y in 𝕎(L, χ₁, x)；hm : m in 𝕎(M, χ₂, x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.weight_vector_multiplication`：∀ {R : Type u_2} {L : Type u_3} 
[inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (M₁ : Type u_
5)   (M₂ : Type u_6) (M₃ : T…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.toModuleHom_apply`：toModuleHom_apply (x : L) (m : M) : toModul
eHom R L M (x otimesₜ m) = ⁅x, m⁆
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lie_mem_maxGenEigenspace_toEnd
    {χ₁ χ₂ : R} {x y : L} {m : M} (hy : y ∈ 𝕎(L, χ₁, x)) (hm : m ∈ 𝕎(M, χ₂, x)) :
    ⁅y, m⁆ ∈ 𝕎(M, χ₁ + χ₂, x) := by
  apply LieModule.weight_vector_multiplication L M M (toModuleHom R L M) χ₁ χ₂
  simp only [LieModuleHom.coe_toLinearMap, Function.comp_apply, LinearMap.coe_comp,
    TensorProduct.mapIncl, LinearMap.mem_range]
  use ⟨y, hy⟩ ⊗ₜ ⟨m, hm⟩
  simp only [Submodule.subtype_apply, toModuleHom_apply, TensorProduct.map_tmul]

variable (M)

/-- If `M` is a representation of a nilpotent Lie algebra `L`, `χ` is a scalar, and `x : L`, then
`genWeightSpaceOf M χ x` is the maximal generalized `χ`-eigenspace of the action of `x` on `M`.

It is a Lie submodule because `L` is nilpotent. -/
/-
**LieModule.genWeightSpaceOf** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：genWeightSpaceOf [LieRing.IsNilpotent L] (χ : R) (x : L) : LieSubmodule R 
L M
参数：χ : R；x : L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is a representation of a nilpotent Lie algebra `L`, `χ` is a scalar, and 
`x : L`, then
`genWeightSpaceOf M χ x` is the maximal generalized `χ`-eigenspace of the action
 of `x` on `M`.

It is a Lie submodule because `L` is nilpotent.
-/
def genWeightSpaceOf [LieRing.IsNilpotent L] (χ : R) (x : L) : LieSubmodule R L M :=
  { 𝕎(M, χ, x) with
    lie_mem := by
      intro y m hm
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid] at hm ⊢
      rw [← zero_add χ]
      exact lie_mem_maxGenEigenspace_toEnd (by simp) hm }

end notation_genWeightSpaceOf

variable (M)
variable [LieRing.IsNilpotent L]

/-
**LieModule.mem_genWeightSpaceOf** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：mem_genWeightSpaceOf (χ : R) (x : L) (m : M) : m in genWeightSpaceOf M χ x
 ↔ exists k : Nat, ((toEnd R L M x - χ • ↑1) ^ k) m = 0
参数：χ : R；x : L；m : M。
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
theorem mem_genWeightSpaceOf (χ : R) (x : L) (m : M) :
    m ∈ genWeightSpaceOf M χ x ↔ ∃ k : ℕ, ((toEnd R L M x - χ • ↑1) ^ k) m = 0 := by
  simp [genWeightSpaceOf]
/-
**LieModule.coe_genWeightSpaceOf_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：coe_genWeightSpaceOf_zero (x : L) : ↑(genWeightSpaceOf M (0 : R) x) = ⨆ k,
 LinearMap.ker (toEnd R L M x ^ k)
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Module.End.genEigenspace_zero_nat`：genEigenspace_zero_nat (f : End R M) 
(k : Nat) : f.genEigenspace 0 k = LinearMap.ker (f ^ k)
· 使用定理 `LieSubmodule.mk.congr_simp`：∀ {R : Type u} {L : Type v} {M : Type w} [in
st : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _roo
t_.Module R M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_genWeightSpaceOf_zero (x : L) :
    ↑(genWeightSpaceOf M (0 : R) x) = ⨆ k, LinearMap.ker (toEnd R L M x ^ k) := by
  simp [genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq]

/-- If `M` is a representation of a nilpotent Lie algebra `L`
and `χ : L → R` is a family of scalars,
then `genWeightSpace M χ` is the intersection of the maximal generalized `χ x`-eigenspaces
of the action of `x` on `M` as `x` ranges over `L`.

It is a Lie submodule because `L` is nilpotent. -/
/-
**LieModule.genWeightSpace** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：genWeightSpace (χ : L -> R) : LieSubmodule R L M
参数：χ : L -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is a representation of a nilpotent Lie algebra `L`
and `χ : L → R` is a family of scalars,
then `genWeightSpace M χ` is the intersection of the maximal generalized `χ x`-e
igenspaces
of the action of `x` on `M` as `x` ranges over `L`.

It is a Lie submodule because `L` is nilpotent.
-/
def genWeightSpace (χ : L → R) : LieSubmodule R L M :=
  ⨅ x, genWeightSpaceOf M (χ x) x
/-
**LieModule.mem_genWeightSpace** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：mem_genWeightSpace (χ : L -> R) (m : M) : m in genWeightSpace M χ ↔ forall
 x, exists k : Nat, ((toEnd R L M x - χ x • ↑1) ^ k) m = 0
参数：χ : L -> R；m : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_genWeightSpace (χ : L → R) (m : M) :
    m ∈ genWeightSpace M χ ↔ ∀ x, ∃ k : ℕ, ((toEnd R L M x - χ x • ↑1) ^ k) m = 0 := by
  simp [genWeightSpace, mem_genWeightSpaceOf]
/-
**LieModule.genWeightSpace_le_genWeightSpaceOf** 是 Mathlib 中的一个引理，位于命名空间 `LieMod
ule`。
形式化陈述：genWeightSpace_le_genWeightSpaceOf (x : L) (χ : L -> R) : genWeightSpace M
 χ <= genWeightSpaceOf M (χ x) x
参数：x : L；χ : L -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
lemma genWeightSpace_le_genWeightSpaceOf (x : L) (χ : L → R) :
    genWeightSpace M χ ≤ genWeightSpaceOf M (χ x) x :=
  iInf_le _ x
/-
**LieModule.weightSpace_le_genWeightSpace** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：weightSpace_le_genWeightSpace (χ : L -> R) : weightSpace M χ <= genWeightS
pace M χ
参数：χ : L -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma weightSpace_le_genWeightSpace (χ : L → R) :
    weightSpace M χ ≤ genWeightSpace M χ := by
  apply le_iInf
  intro x
  rw [← (LieSubmodule.toSubmodule_orderEmbedding R L M).le_iff_le]
  apply (iInf_le _ x).trans
  exact ((toEnd R L M x).genEigenspace (χ x)).monotone le_top

variable (R L) in
/-- A weight of a Lie module is a map `L → R` such that the corresponding weight space is
non-trivial. -/
/-
**LieModule.Weight** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieModule`。
形式化陈述：(R : Type u_2) →   (L : Type u_3) →     (M : Type u_4) →       [inst : Com
mRing R] →         [inst_1 : LieRing L] →           [inst_2 : LieAlgebra R L] → 
            [inst_3 : AddCommGroup M] →               [inst_4 : _root_.Module R 
M] →                 [inst_5 : LieRingModule L M] → [LieModule R L M] → [LieRing
.IsNilpotent L] → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weight of a Lie module is a map `L → R` such that the corresponding weight spa
ce is
non-trivial.
-/
structure Weight where
  /-- The family of eigenvalues corresponding to a weight. -/
  toFun : L → R
  genWeightSpace_ne_bot' : genWeightSpace M toFun ≠ ⊥

namespace Weight

/-
**LieModule.Weight.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `LieModule.Weight`。
形式化陈述：instFunLike : FunLike (Weight R L M) L R where coe χ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (Weight R L M) L R where
  coe χ := χ.1
  coe_injective χ₁ χ₂ h := by cases χ₁; cases χ₂; simp_all
/-
**LieModule.Weight.coe_weight_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieModule.Weight`。
形式化陈述：∀ {R : Type u_2} {L : Type u_3} (M : Type u_4) [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] (χ : L → R) (h : LieModule.genWeightSpace M χ ≠ ⊥), 
  ⇑{ toFun := χ, genWeightSpace_ne_bot' := h } = χ
参数：M : Type u_4；χ : L → R；h : LieModule.genWeightSpace M χ ≠ ⊥。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_weight_mk (χ : L → R) (h) :
    (↑(⟨χ, h⟩ : Weight R L M) : L → R) = χ :=
  rfl
/-
**LieModule.Weight.genWeightSpace_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.We
ight`。
形式化陈述：genWeightSpace_ne_bot (χ : Weight R L M) : genWeightSpace M χ != ⊥
参数：χ : Weight R L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.Weight.genWeightSpace_ne_bot'`：∀ {R : Type u_2} {L : Type u_3}
 {M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R 
L]   [inst_3 : AddCommGroup M…
-/
lemma genWeightSpace_ne_bot (χ : Weight R L M) : genWeightSpace M χ ≠ ⊥ := χ.genWeightSpace_ne_bot'

variable {M}
/-
**LieModule.Weight.ext** 是 Mathlib 中的一个定理，位于命名空间 `LieModule.Weight`。
形式化陈述：∀ {R : Type u_2} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] {χ₁ χ₂ : LieModule.Weight R L M}, (∀ (x : L), χ₁ x =
 χ₂ x) → χ₁ = χ₂
参数：∀ (x : L), χ₁ x = χ₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
@[ext] lemma ext {χ₁ χ₂ : Weight R L M} (h : ∀ x, χ₁ x = χ₂ x) : χ₁ = χ₂ := DFunLike.ext _ _ h
/-
**LieModule.Weight.ext_iff'** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.Weight`。
形式化陈述：ext_iff' {χ₁ χ₂ : Weight R L M} : (χ₁ : L -> R) = χ₂ ↔ χ₁ = χ₂
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
lemma ext_iff' {χ₁ χ₂ : Weight R L M} : (χ₁ : L → R) = χ₂ ↔ χ₁ = χ₂ := by simp
/-
**LieModule.Weight.exists_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.Weight`。
形式化陈述：exists_ne_zero (χ : Weight R L M) : exists x in genWeightSpace M χ, x != 0
参数：χ : Weight R L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `LieModule.Weight.genWeightSpace_ne_bot`：genWeightSpace_ne_bot (χ : Weigh
t R L M) : genWeightSpace M χ != ⊥
-/
lemma exists_ne_zero (χ : Weight R L M) :
    ∃ x ∈ genWeightSpace M χ, x ≠ 0 := by
  simpa [LieSubmodule.eq_bot_iff] using χ.genWeightSpace_ne_bot
/-
**LieModule.Weight.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule.Weight`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton M] : IsEmpty (Weight R L M) :=
  ⟨fun h ↦ h.2 (Subsingleton.elim _ _)⟩
/-
**LieModule.Weight.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule.Weight`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial (genWeightSpace M (0 : L → R))] : Zero (Weight R L M) :=
  ⟨0, fun e ↦ not_nontrivial (⊥ : LieSubmodule R L M) (e ▸ ‹_›)⟩
/-
**LieModule.Weight.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule.Weight`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial (genWeightSpace M (0 : L → R))] : IsZeroApply (Weight R L M) L R where
  zero_apply _ := rfl

@[deprecated (since := "2026-07-27")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-27")] protected alias zero_apply := zero_apply

/-- The proposition that a weight of a Lie module is zero.

We make this definition because we cannot define a `Zero (Weight R L M)` instance since the weight
space of the zero function can be trivial. -/
/-
**LieModule.Weight.IsZero** 是 Mathlib 中的一个定义，位于命名空间 `LieModule.Weight`。
形式化陈述：IsZero (χ : Weight R L M)
参数：χ : Weight R L M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a weight of a Lie module is zero.

We make this definition because we cannot define a `Zero (Weight R L M)` instanc
e since the weight
space of the zero function can be trivial.
-/
def IsZero (χ : Weight R L M) := (χ : L → R) = 0
/-
**LieModule.Weight.IsZero.eq** 是 Mathlib 中的一个定理，位于命名空间 `LieModule.Weight.IsZero`
。
形式化陈述：∀ {R : Type u_2} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] {χ : LieModule.Weight R L M}, χ.IsZero → ⇑χ = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma IsZero.eq {χ : Weight R L M} (hχ : χ.IsZero) : (χ : L → R) = 0 := hχ
/-
**LieModule.Weight.coe_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieModule.Weight`。
形式化陈述：∀ {R : Type u_2} {L : Type u_3} {M : Type u_4} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] (χ : LieModule.Weight R L M), ⇑χ = 0 ↔ χ.IsZero
参数：χ : LieModule.Weight R L M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma coe_eq_zero_iff (χ : Weight R L M) : (χ : L → R) = 0 ↔ χ.IsZero := Iff.rfl
/-
**LieModule.Weight.isZero_iff_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.Weigh
t`。
形式化陈述：isZero_iff_eq_zero [Nontrivial (genWeightSpace M (0 : L -> R))] {χ : Weigh
t R L M} : χ.IsZero ↔ χ = 0
参数：genWeightSpace M (0 : L -> R)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.Weight.ext_iff'`：ext_iff' {χ₁ χ₂ : Weight R L M} : (χ₁ : L -> 
R) = χ₂ ↔ χ₁ = χ₂
-/
lemma isZero_iff_eq_zero [Nontrivial (genWeightSpace M (0 : L → R))] {χ : Weight R L M} :
    χ.IsZero ↔ χ = 0 := Weight.ext_iff' (χ₂ := 0)
/-
**LieModule.Weight.isZero_zero** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.Weight`。
形式化陈述：isZero_zero [Nontrivial (genWeightSpace M (0 : L -> R))] : IsZero (0 : Wei
ght R L M)
参数：genWeightSpace M (0 : L -> R)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isZero_zero [Nontrivial (genWeightSpace M (0 : L → R))] : IsZero (0 : Weight R L M) := rfl

/-- The proposition that a weight of a Lie module is non-zero. -/
/-
**LieModule.Weight.IsNonZero** 是 Mathlib 中的一个缩写定义，位于命名空间 `LieModule.Weight`。
形式化陈述：IsNonZero (χ : Weight R L M)
参数：χ : Weight R L M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a weight of a Lie module is non-zero.
-/
abbrev IsNonZero (χ : Weight R L M) := ¬ IsZero (χ : Weight R L M)
/-
**LieModule.Weight.isNonZero_iff_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.We
ight`。
形式化陈述：isNonZero_iff_ne_zero [Nontrivial (genWeightSpace M (0 : L -> R))] {χ : We
ight R L M} : χ.IsNonZero ↔ χ != 0
参数：genWeightSpace M (0 : L -> R)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `LieModule.Weight.isZero_iff_eq_zero`：isZero_iff_eq_zero [Nontrivial (gen
WeightSpace M (0 : L -> R))] {χ : Weight R L M} : χ.IsZero ↔ χ = 0
-/
lemma isNonZero_iff_ne_zero [Nontrivial (genWeightSpace M (0 : L → R))] {χ : Weight R L M} :
    χ.IsNonZero ↔ χ ≠ 0 := isZero_iff_eq_zero.not
/-
**LieModule.Weight.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule.Weight`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : DecidablePred (IsNonZero (R := R) (L := L) (M := M)) := Classical.decPred _

variable (R L M) in
/-- The set of weights is equivalent to a subtype. -/
/-
**LieModule.Weight.equivSetOfPred** 是 Mathlib 中的一个定义，位于命名空间 `LieModule.Weight`。
形式化陈述：equivSetOfPred : Weight R L M ≃ {χ : L -> R | genWeightSpace M χ != ⊥} whe
re toFun w
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.Weight.genWeightSpace_ne_bot'`：∀ {R : Type u_2} {L : Type u_3}
 {M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R 
L]   [inst_3 : AddCommGroup M…

--- 原说明 ---
The set of weights is equivalent to a subtype.
-/
def equivSetOfPred : Weight R L M ≃ {χ : L → R | genWeightSpace M χ ≠ ⊥} where
  toFun w := ⟨w.1, w.2⟩
  invFun w := ⟨w.1, w.2⟩
  left_inv w := by simp
  right_inv w := by simp

@[deprecated (since := "2026-07-09")] alias equivSetOf := equivSetOfPred
/-
**LieModule.Weight.genWeightSpaceOf_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.
Weight`。
形式化陈述：genWeightSpaceOf_ne_bot (χ : Weight R L M) (x : L) : genWeightSpaceOf M (χ
 x) x != ⊥
参数：χ : Weight R L M；x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.Weight.genWeightSpace_ne_bot`：genWeightSpace_ne_bot (χ : Weigh
t R L M) : genWeightSpace M χ != ⊥
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
lemma genWeightSpaceOf_ne_bot (χ : Weight R L M) (x : L) :
    genWeightSpaceOf M (χ x) x ≠ ⊥ := by
  have : ⨅ x, genWeightSpaceOf M (χ x) x ≠ ⊥ := χ.genWeightSpace_ne_bot
  contrapose this
  rw [eq_bot_iff]
  exact le_of_le_of_eq (iInf_le _ _) this
/-
**LieModule.Weight.hasEigenvalueAt** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.Weight`。
形式化陈述：hasEigenvalueAt (χ : Weight R L M) (x : L) : (toEnd R L M x).HasEigenvalue
 (χ x)
参数：χ : Weight R L M；x : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.mk.congr_simp`：∀ {R : Type u} {L : Type v} {M : Type w} [in
st : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _roo
t_.Module R M] […
· 使用引理 `LieModule.Weight.genWeightSpaceOf_ne_bot`：genWeightSpaceOf_ne_bot (χ : W
eight R L M) (x : L) : genWeightSpaceOf M (χ x) x != ⊥
· 使用定理 `Module.End.hasEigenvalue_of_hasGenEigenvalue`：hasEigenvalue_of_hasGenEig
envalue {f : End R M} {μ : R} {k : Nat} (hμ : f.HasGenEigenvalue μ k) : f.HasEig
envalue μ
-/
lemma hasEigenvalueAt (χ : Weight R L M) (x : L) :
    (toEnd R L M x).HasEigenvalue (χ x) := by
  obtain ⟨k : ℕ, hk : (toEnd R L M x).genEigenspace (χ x) k ≠ ⊥⟩ := by
    simpa [genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq] using χ.genWeightSpaceOf_ne_bot x
  exact Module.End.hasEigenvalue_of_hasGenEigenvalue hk
/-
**LieModule.Weight.apply_eq_zero_of_isNilpotent** 是 Mathlib 中的一个引理，位于命名空间 `LieMo
dule.Weight`。
形式化陈述：apply_eq_zero_of_isNilpotent [IsDomain R] [Module.IsTorsionFree R M] [IsRe
duced R] (x : L) (h : _root_.IsNilpotent (toEnd R L M x)) (χ : Weight R L M) : χ
 x = 0
参数：x : L；h : _root_.IsNilpotent (toEnd R L M x)；χ : Weight R L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNilpotent.eq_zero`：IsNilpotent.eq_zero [Zero R] [Pow R Nat] [IsReduced
 R] (h : IsNilpotent x) : x = 0
· 使用定理 `Module.End.HasEigenvalue.isNilpotent_of_isNilpotent`：∀ {R : Type v} {M :
 Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R
 M] [IsDomain R]   [Module.IsTorsionFree …
· 使用引理 `LieModule.Weight.hasEigenvalueAt`：hasEigenvalueAt (χ : Weight R L M) (x 
: L) : (toEnd R L M x).HasEigenvalue (χ x)
-/
lemma apply_eq_zero_of_isNilpotent [IsDomain R] [Module.IsTorsionFree R M] [IsReduced R]
    (x : L) (h : _root_.IsNilpotent (toEnd R L M x)) (χ : Weight R L M) :
    χ x = 0 :=
  ((χ.hasEigenvalueAt x).isNilpotent_of_isNilpotent h).eq_zero

end Weight

/-- See also the more useful form `LieModule.zero_genWeightSpace_eq_top_of_nilpotent`. -/
@[simp]
/-
**LieModule.zero_genWeightSpace_eq_top_of_nilpotent'** 是 Mathlib 中的一个定理，位于命名空间 `
LieModule`。
形式化陈述：zero_genWeightSpace_eq_top_of_nilpotent' [IsNilpotent L M] : genWeightSpac
e M (0 : L -> R) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LieModule.maxGenEigenSpace_toEnd_eq_top`：∀ (R : Type u) (L : Type v) (M 
: Type w) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [
inst_3 : AddCommGroup M] [ins…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LieSubmodule.mk.congr_simp`：∀ {R : Type u} {L : Type v} {M : Type w} [in
st : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _roo
t_.Module R M] […
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
See also the more useful form `LieModule.zero_genWeightSpace_eq_top_of_nilpotent
`.
-/
theorem zero_genWeightSpace_eq_top_of_nilpotent' [IsNilpotent L M] :
    genWeightSpace M (0 : L → R) = ⊤ := by
  simp [genWeightSpace, genWeightSpaceOf]
/-
**LieModule.coe_genWeightSpace_of_top** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：coe_genWeightSpace_of_top (χ : L -> R) : (genWeightSpace M (χ ∘ (⊤ : LieSu
balgebra R L).incl) : Submodule R M) = genWeightSpace M χ
参数：χ : L -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `instIsNilpotentSubtypeMemLieSubalgebraTop`：∀ {R : Type u} {L : Type v} [
inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [h : LieRing
.IsNilpotent L], LieRing.IsNilp…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coe_genWeightSpace_of_top (χ : L → R) :
    (genWeightSpace M (χ ∘ (⊤ : LieSubalgebra R L).incl) : Submodule R M) = genWeightSpace M χ := by
  ext m
  simp only [mem_genWeightSpace, LieSubmodule.mem_toSubmodule, Subtype.forall]
  apply forall_congr'
  simp

@[simp]
/-
**LieModule.zero_genWeightSpace_eq_top_of_nilpotent** 是 Mathlib 中的一个定理，位于命名空间 `L
ieModule`。
形式化陈述：zero_genWeightSpace_eq_top_of_nilpotent [IsNilpotent L M] : genWeightSpace
 M (0 : (⊤ : LieSubalgebra R L) -> R) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsNilpotentSubtypeMemLieSubalgebraTop`：∀ {R : Type u} {L : Type v} [
inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [h : LieRing
.IsNilpotent L], LieRing.IsNilp…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.zero_genWeightSpace_eq_top_of_nilpotent'`：zero_genWeightSpace_
eq_top_of_nilpotent' [IsNilpotent L M] : genWeightSpace M (0 : L -> R) = ⊤
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_genWeightSpace_eq_top_of_nilpotent [IsNilpotent L M] :
    genWeightSpace M (0 : (⊤ : LieSubalgebra R L) → R) = ⊤ := by
  simp_all
/-
**LieModule.exists_genWeightSpace_le_ker_of_isNoetherian** 是 Mathlib 中的一个定理，位于命名
空间 `LieModule`。
形式化陈述：exists_genWeightSpace_le_ker_of_isNoetherian [IsNoetherian R M] (χ : L -> 
R) (x : L) : exists k : Nat, genWeightSpace M χ <= ((toEnd R L M x - algebraMap 
R _ (χ x)) ^ k).ker
参数：χ : L -> R；x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.genWeightSpace_le_genWeightSpaceOf`：genWeightSpace_le_genWeigh
tSpaceOf (x : L) (χ : L -> R) : genWeightSpace M χ <= genWeightSpaceOf M (χ x) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.genEigenspace_nat`：genEigenspace_nat {f : End R M} {μ : R} {k
 : Nat} : f.genEigenspace μ k = LinearMap.ker ((f - μ • 1) ^ k)
· 使用定理 `Module.End.maxGenEigenspace_eq`：maxGenEigenspace_eq [IsNoetherian R M] (
f : End R M) (μ : R) : maxGenEigenspace f μ = f.genEigenspace μ (maxGenEigenspac
eIndex f μ)
-/
theorem exists_genWeightSpace_le_ker_of_isNoetherian [IsNoetherian R M] (χ : L → R) (x : L) :
    ∃ k : ℕ,
      genWeightSpace M χ ≤ ((toEnd R L M x - algebraMap R _ (χ x)) ^ k).ker := by
  use (toEnd R L M x).maxGenEigenspaceIndex (χ x)
  intro m hm
  replace hm : m ∈ (toEnd R L M x).maxGenEigenspace (χ x) :=
    genWeightSpace_le_genWeightSpaceOf M x χ hm
  rwa [Module.End.maxGenEigenspace_eq, Module.End.genEigenspace_nat] at hm

variable (R) in
/-
**LieModule.exists_genWeightSpace_zero_le_ker_of_isNoetherian** 是 Mathlib 中的一个定理
，位于命名空间 `LieModule`。
形式化陈述：exists_genWeightSpace_zero_le_ker_of_isNoetherian [IsNoetherian R M] (x : 
L) : exists k : Nat, genWeightSpace M (0 : L -> R) <= LinearMap.ker (toEnd R L M
 x ^ k)
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `LieModule.exists_genWeightSpace_le_ker_of_isNoetherian`：exists_genWeight
Space_le_ker_of_isNoetherian [IsNoetherian R M] (χ : L -> R) (x : L) : exists k 
: Nat, genWeightSpace M χ <= ((toEnd R L M x…
-/
theorem exists_genWeightSpace_zero_le_ker_of_isNoetherian
    [IsNoetherian R M] (x : L) :
    ∃ k : ℕ, genWeightSpace M (0 : L → R) ≤ LinearMap.ker (toEnd R L M x ^ k) := by
  simpa using exists_genWeightSpace_le_ker_of_isNoetherian M (0 : L → R) x
/-
**LieModule.isNilpotent_toEnd_sub_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `LieModul
e`。
形式化陈述：isNilpotent_toEnd_sub_algebraMap [IsNoetherian R M] (χ : L -> R) (x : L) :
 _root_.IsNilpotent toEnd R L (genWeightSpace M χ) x - algebraMap R _ (χ x)
参数：χ : L -> R；x : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `LieModule.exists_genWeightSpace_le_ker_of_isNoetherian`：exists_genWeight
Space_le_ker_of_isNoetherian [IsNoetherian R M] (χ : L -> R) (x : L) : exists k 
: Nat, genWeightSpace M χ <= ((toEnd R L M x…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Module.End.pow_apply_mem_of_forall_mem`：∀ {R : Type u_1} {M : Type u_5} 
[inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {f
' : M →ₗ[R] M} {p : Submodul…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.pow_restrict`：∀ {R : Type u_1} {M : Type u_5} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {f' : M →ₗ[R] M} 
{p : Submodul…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZeroMemClass.coe_eq_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLi
ke A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] {S' : A} {x : ↥S'},   ↑x = 
0 ↔ x = 0
-/
lemma isNilpotent_toEnd_sub_algebraMap [IsNoetherian R M] (χ : L → R) (x : L) :
    _root_.IsNilpotent <| toEnd R L (genWeightSpace M χ) x - algebraMap R _ (χ x) := by
  have : toEnd R L (genWeightSpace M χ) x - algebraMap R _ (χ x) =
      (toEnd R L M x - algebraMap R _ (χ x)).restrict
        (fun m hm ↦ sub_mem (LieSubmodule.lie_mem _ hm) (Submodule.smul_mem _ _ hm)) := by
    rfl
  obtain ⟨k, hk⟩ := exists_genWeightSpace_le_ker_of_isNoetherian M χ x
  use k
  ext ⟨m, hm⟩
  simp only [this, Module.End.pow_restrict _, LinearMap.zero_apply, ZeroMemClass.coe_zero,
    ZeroMemClass.coe_eq_zero]
  exact ZeroMemClass.coe_eq_zero.mp (hk hm)

/-- A (nilpotent) Lie algebra acts nilpotently on the zero weight space of a Noetherian Lie
module. -/
/-
**LieModule.isNilpotent_toEnd_genWeightSpace_zero** 是 Mathlib 中的一个定理，位于命名空间 `Lie
Module`。
形式化陈述：isNilpotent_toEnd_genWeightSpace_zero [IsNoetherian R M] (x : L) : _root_.
IsNilpotent toEnd R L (genWeightSpace M (0 : L -> R)) x
参数：x : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `LieModule.isNilpotent_toEnd_sub_algebraMap`：isNilpotent_toEnd_sub_algebr
aMap [IsNoetherian R M] (χ : L -> R) (x : L) : _root_.IsNilpotent toEnd R L (gen
WeightSpace M χ) x - algebraMap …

--- 原说明 ---
A (nilpotent) Lie algebra acts nilpotently on the zero weight space of a Noether
ian Lie
module.
-/
theorem isNilpotent_toEnd_genWeightSpace_zero [IsNoetherian R M] (x : L) :
    _root_.IsNilpotent <| toEnd R L (genWeightSpace M (0 : L → R)) x := by
  simpa using isNilpotent_toEnd_sub_algebraMap M (0 : L → R) x

/-- By Engel's theorem, the zero weight space of a Noetherian Lie module is nilpotent. -/
/-
**LieModule.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
By Engel's theorem, the zero weight space of a Noetherian Lie module is nilpoten
t.
-/
instance [IsNoetherian R M] :
    IsNilpotent L (genWeightSpace M (0 : L → R)) :=
  isNilpotent_iff_forall'.mpr <| isNilpotent_toEnd_genWeightSpace_zero M

variable (R L)

@[simp]
/-
**LieModule.genWeightSpace_zero_normalizer_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Li
eModule`。
形式化陈述：genWeightSpace_zero_normalizer_eq_self : (genWeightSpace M (0 : L -> R)).n
ormalizer = genWeightSpace M 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `LieSubmodule.mem_normalizer`：mem_normalizer (m : M) : m in N.normalizer 
↔ forall x : L, ⁅x, m⁆ in N
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `LieSubmodule.le_normalizer`：le_normalizer : N <= N.normalizer
-/
lemma genWeightSpace_zero_normalizer_eq_self :
    (genWeightSpace M (0 : L → R)).normalizer = genWeightSpace M 0 := by
  refine le_antisymm ?_ (LieSubmodule.le_normalizer _)
  intro m hm
  rw [LieSubmodule.mem_normalizer] at hm
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm ⊢
  intro y
  obtain ⟨k, hk⟩ := hm y y
  use k + 1
  simpa [pow_succ, Module.End.mul_eq_comp]
/-
**LieModule.iSup_ucs_le_genWeightSpace_zero** 是 Mathlib 中的一个引理，位于命名空间 `LieModule
`。
形式化陈述：iSup_ucs_le_genWeightSpace_zero : ⨆ k, (⊥ : LieSubmodule R L M).ucs k <= g
enWeightSpace M (0 : L -> R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ucs_le_of_normalizer_eq_self`：ucs_le_of_normalizer_eq_self 
(h : N₁.normalizer = N₁) (k : Nat) : (⊥ : LieSubmodule R L M).ucs k <= N₁
· 使用引理 `LieModule.genWeightSpace_zero_normalizer_eq_self`：genWeightSpace_zero_no
rmalizer_eq_self : (genWeightSpace M (0 : L -> R)).normalizer = genWeightSpace M
 0
-/
lemma iSup_ucs_le_genWeightSpace_zero :
    ⨆ k, (⊥ : LieSubmodule R L M).ucs k ≤ genWeightSpace M (0 : L → R) := by
  simpa using
    LieSubmodule.ucs_le_of_normalizer_eq_self (genWeightSpace_zero_normalizer_eq_self R L M)

/-- See also `LieModule.iInf_lowerCentralSeries_eq_posFittingComp`. -/
/-
**LieModule.iSup_ucs_eq_genWeightSpace_zero** 是 Mathlib 中的一个引理，位于命名空间 `LieModule
`。
形式化陈述：iSup_ucs_eq_genWeightSpace_zero [IsNoetherian R M] : ⨆ k, (⊥ : LieSubmodul
e R L M).ucs k = genWeightSpace M (0 : L -> R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieSubmodule.isNilpotent_iff_exists_self_le_ucs`：isNilpotent_iff_exists_
self_le_ucs : LieModule.IsNilpotent L N ↔ exists k, N <= (⊥ : LieSubmodule R L M
).ucs k
· 使用定理 `LieModule.instIsNilpotentSubtypeMemLieSubmoduleGenWeightSpaceOfNatForall
OfIsNoetherian`：∀ {R : Type u_2} {L : Type u_3} (M : Type u_4) [inst : CommRing 
R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `LieModule.iSup_ucs_le_genWeightSpace_zero`：iSup_ucs_le_genWeightSpace_ze
ro : ⨆ k, (⊥ : LieSubmodule R L M).ucs k <= genWeightSpace M (0 : L -> R)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f

--- 原说明 ---
See also `LieModule.iInf_lowerCentralSeries_eq_posFittingComp`.
-/
lemma iSup_ucs_eq_genWeightSpace_zero [IsNoetherian R M] :
    ⨆ k, (⊥ : LieSubmodule R L M).ucs k = genWeightSpace M (0 : L → R) := by
  obtain ⟨k, hk⟩ := (LieSubmodule.isNilpotent_iff_exists_self_le_ucs
    <| genWeightSpace M (0 : L → R)).mp inferInstance
  refine le_antisymm (iSup_ucs_le_genWeightSpace_zero R L M) (le_trans hk ?_)
  exact le_iSup (fun k ↦ (⊥ : LieSubmodule R L M).ucs k) k

variable {L}

/-- If `M` is a representation of a nilpotent Lie algebra `L`, and `x : L`, then
`posFittingCompOf R M x` is the infimum of the decreasing system
`range φₓ ⊇ range φₓ² ⊇ range φₓ³ ⊇ ⋯` where `φₓ : End R M := toEnd R L M x`. We call this
the "positive Fitting component" because with appropriate assumptions (e.g., `R` is a field and
`M` is finite-dimensional) `φₓ` induces the so-called Fitting decomposition: `M = M₀ ⊕ M₁` where
`M₀ = genWeightSpaceOf M 0 x` and `M₁ = posFittingCompOf R M x`.

It is a Lie submodule because `L` is nilpotent. -/
/-
**LieModule.posFittingCompOf** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：posFittingCompOf (x : L) : LieSubmodule R L M
参数：x : L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is a representation of a nilpotent Lie algebra `L`, and `x : L`, then
`posFittingCompOf R M x` is the infimum of the decreasing system
`range φₓ ⊇ range φₓ² ⊇ range φₓ³ ⊇ ⋯` where `φₓ : End R M := toEnd R L M x`. We
 call this
the "positive Fitting component" because with appropriate assumptions (e.g., `R`
 is a field and
`M` is finite-dimensional) `φₓ` induces the so-called Fitting decomposition: `M 
= M₀ ⊕ M₁` where
`M₀ = genWeightSpaceOf M 0 x` and `M₁ = posFittingCompOf R M x`.

It is a Lie submodule because `L` is nilpotent.
-/
def posFittingCompOf (x : L) : LieSubmodule R L M :=
  { toSubmodule := ⨅ k, LinearMap.range (toEnd R L M x ^ k)
    lie_mem := by
      set φ := toEnd R L M x
      intro y m hm
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, Submodule.mem_iInf, LinearMap.mem_range] at hm ⊢
      intro k
      obtain ⟨N, hN⟩ := LieAlgebra.nilpotent_ad_of_nilpotent_algebra R L
      obtain ⟨m, rfl⟩ := hm (N + k)
      let f₁ : Module.End R (L ⊗[R] M) := (LieAlgebra.ad R L x).rTensor M
      let f₂ : Module.End R (L ⊗[R] M) := φ.lTensor L
      replace hN : f₁ ^ N = 0 := by ext; simp [f₁, hN]
      have h₁ : Commute f₁ f₂ := by ext; simp [f₁, f₂]
      have h₂ : φ ∘ₗ toModuleHom R L M = toModuleHom R L M ∘ₗ (f₁ + f₂) := by ext; simp [φ, f₁, f₂]
      obtain ⟨q, hq⟩ := h₁.add_pow_dvd_pow_of_pow_eq_zero_right (N + k).le_succ hN
      use toModuleHom R L M (q (y ⊗ₜ m))
      change (φ ^ k).comp ((toModuleHom R L M : L ⊗[R] M →ₗ[R] M)) _ = _
      simp [φ, f₁, f₂, Module.End.commute_pow_left_of_commute h₂,
        LinearMap.comp_apply (g := (f₁ + f₂) ^ k), ← LinearMap.comp_apply (g := q),
        ← Module.End.mul_eq_comp, ← hq] }

variable {M} in
/-
**LieModule.mem_posFittingCompOf** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：mem_posFittingCompOf (x : L) (m : M) : m in posFittingCompOf R M x ↔ foral
l (k : Nat), exists n, (toEnd R L M x ^ k) n = m
参数：x : L；m : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_posFittingCompOf (x : L) (m : M) :
    m ∈ posFittingCompOf R M x ↔ ∀ (k : ℕ), ∃ n, (toEnd R L M x ^ k) n = m := by
  simp [posFittingCompOf]
/-
**LieModule.posFittingCompOf_le_lowerCentralSeries** 是 Mathlib 中的一个定理，位于命名空间 `Li
eModule`。
形式化陈述：∀ (R : Type u_2) {L : Type u_3} (M : Type u_4) [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] (x : L) (k : ℕ),   LieModule.posFittingCompOf R M x 
≤ LieModule.lowerCentralSeries R L M k
参数：R : Type u_2；M : Type u_4；x : L；k : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieModule.lowerCentralSeries_succ`：lowerCentralSeries_succ : lowerCentra
lSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `LieSubmodule.lie_mem_lie`：lie_mem_lie {x : L} {m : M} (hx : x in I) (hm 
: m in N) : ⁅x, m⁆ in ⁅I, N⁆
· 使用定理 `LieSubmodule.mem_top`：mem_top (x : M) : x in (⊤ : LieSubmodule R L M)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LieModule.mem_posFittingCompOf`：mem_posFittingCompOf (x : L) (m : M) : m
 in posFittingCompOf R M x ↔ forall (k : Nat), exists n, (toEnd R L M x ^ k) n =
 m
-/
@[simp] lemma posFittingCompOf_le_lowerCentralSeries (x : L) (k : ℕ) :
    posFittingCompOf R M x ≤ lowerCentralSeries R L M k := by
  suffices ∀ m l, (toEnd R L M x ^ l) m ∈ lowerCentralSeries R L M l by
    intro m hm
    obtain ⟨n, rfl⟩ := (mem_posFittingCompOf R x m).mp hm k
    exact this n k
  intro m l
  induction l with
  | zero => simp
  | succ l ih =>
    simp only [lowerCentralSeries_succ, pow_succ', Module.End.mul_apply]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) ih
/-
**LieModule.posFittingCompOf_eq_bot_of_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 `Li
eModule`。
形式化陈述：∀ (R : Type u_2) {L : Type u_3} (M : Type u_4) [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [LieModule.IsNilpotent L M] (x : L), LieModule.posFi
ttingCompOf R M x = ⊥
参数：R : Type u_2；M : Type u_4；x : L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
@[simp] lemma posFittingCompOf_eq_bot_of_isNilpotent
    [IsNilpotent L M] (x : L) :
    posFittingCompOf R M x = ⊥ := by
  simp_rw [eq_bot_iff, ← iInf_lowerCentralSeries_eq_bot_of_isNilpotent, le_iInf_iff,
    posFittingCompOf_le_lowerCentralSeries, forall_const]

variable (L)

/-- If `M` is a representation of a nilpotent Lie algebra `L` with coefficients in `R`, then
`posFittingComp R L M` is the span of the positive Fitting components of the action of `x` on `M`,
as `x` ranges over `L`.

It is a Lie submodule because `L` is nilpotent. -/
/-
**LieModule.posFittingComp** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：posFittingComp : LieSubmodule R L M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is a representation of a nilpotent Lie algebra `L` with coefficients in `
R`, then
`posFittingComp R L M` is the span of the positive Fitting components of the act
ion of `x` on `M`,
as `x` ranges over `L`.

It is a Lie submodule because `L` is nilpotent.
-/
def posFittingComp : LieSubmodule R L M :=
  ⨆ x, posFittingCompOf R M x
/-
**LieModule.mem_posFittingComp** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：mem_posFittingComp (m : M) : m in posFittingComp R L M ↔ m in ⨆ (x : L), p
osFittingCompOf R M x
参数：m : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_posFittingComp (m : M) :
    m ∈ posFittingComp R L M ↔ m ∈ ⨆ (x : L), posFittingCompOf R M x := by
  rfl
/-
**LieModule.posFittingCompOf_le_posFittingComp** 是 Mathlib 中的一个引理，位于命名空间 `LieMod
ule`。
形式化陈述：posFittingCompOf_le_posFittingComp (x : L) : posFittingCompOf R M x <= pos
FittingComp R L M
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.posFittingComp.eq_1`：∀ (R : Type u_2) (L : Type u_3) (M : Type
 u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst
_3 : AddCommGroup M…
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma posFittingCompOf_le_posFittingComp (x : L) :
    posFittingCompOf R M x ≤ posFittingComp R L M := by
  rw [posFittingComp]; exact le_iSup (posFittingCompOf R M) x
/-
**LieModule.posFittingComp_le_iInf_lowerCentralSeries** 是 Mathlib 中的一个引理，位于命名空间 
`LieModule`。
形式化陈述：posFittingComp_le_iInf_lowerCentralSeries : posFittingComp R L M <= ⨅ k, l
owerCentralSeries R L M k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma posFittingComp_le_iInf_lowerCentralSeries :
    posFittingComp R L M ≤ ⨅ k, lowerCentralSeries R L M k := by
  simp [posFittingComp]

/-- See also `LieModule.iSup_ucs_eq_genWeightSpace_zero`. -/
/-
**LieModule.iInf_lowerCentralSeries_eq_posFittingComp** 是 Mathlib 中的一个定理，位于命名空间 
`LieModule`。
形式化陈述：∀ (R : Type u_2) (L : Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [IsNoetherian R M] [IsArtinian R M],   ⨅ k, LieModul
e.lowerCentralSeries R L M k = LieModule.posFittingComp R L M
参数：R : Type u_2；L : Type u_3；M : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieModule.iInf_lcs_le_of_isNilpotent_quot`：iInf_lcs_le_of_isNilpotent_qu
ot (h : IsNilpotent L (M ⧸ N)) : ⨅ k, lowerCentralSeries R L M k <= N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.isNilpotent_iff_forall'`：LieModule.isNilpotent_iff_forall' [Is
Noetherian R M] : LieModule.IsNilpotent L M ↔ forall x, _root_.IsNilpotent toEnd
 R L M x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `LinearMap.eventually_iInf_range_pow_eq`：eventually_iInf_range_pow_eq (f 
: Module.End R M) : forallᶠ n in atTop, ⨅ m, LinearMap.range (f ^ m) = LinearMap
.range (f ^ n)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用引理 `LieModule.posFittingCompOf_le_posFittingComp`：posFittingCompOf_le_posFit
tingComp (x : L) : posFittingCompOf R M x <= posFittingComp R L M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Module.End.commute_pow_left_of_commute`：commute_pow_left_of_commute [Sem
iring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₁₂ : R ->+* R₂} {f : M ->ₛₗ[σ₁₂] M
₂} {g : Module.End R M} {g₂ …
· 使用引理 `LieSubmodule.Quotient.toEnd_comp_mk'`：toEnd_comp_mk' (x : L) : LieModule
.toEnd R L (M ⧸ N) x ∘ₗ mk' N = mk' N ∘ₗ LieModule.toEnd R L M x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieSubmodule.Quotient.mk'_apply`：∀ {R : Type u} {L : Type v} {M : Type w
} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 :
 _root_.Module R M] […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `LieModule.posFittingComp_le_iInf_lowerCentralSeries`：posFittingComp_le_i
Inf_lowerCentralSeries : posFittingComp R L M <= ⨅ k, lowerCentralSeries R L M k

--- 原说明 ---
See also `LieModule.iSup_ucs_eq_genWeightSpace_zero`.
-/
@[simp] lemma iInf_lowerCentralSeries_eq_posFittingComp
    [IsNoetherian R M] [IsArtinian R M] :
    ⨅ k, lowerCentralSeries R L M k = posFittingComp R L M := by
  refine le_antisymm ?_ (posFittingComp_le_iInf_lowerCentralSeries R L M)
  apply iInf_lcs_le_of_isNilpotent_quot
  rw [LieModule.isNilpotent_iff_forall' (R := R)]
  intro x
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (toEnd R L M x).eventually_iInf_range_pow_eq
  use k
  ext ⟨m⟩
  set F := posFittingComp R L M
  replace hk : (toEnd R L M x ^ k) m ∈ F := by
    apply posFittingCompOf_le_posFittingComp R L M x
    simp_rw [← LieSubmodule.mem_toSubmodule, posFittingCompOf, hk k (le_refl k)]
    apply LinearMap.mem_range_self
  suffices (toEnd R L (M ⧸ F) x ^ k) (LieSubmodule.Quotient.mk (N := F) m) =
    LieSubmodule.Quotient.mk (N := F) ((toEnd R L M x ^ k) m)
      by simpa [Submodule.Quotient.quot_mk_eq_mk, this]
  have := LinearMap.congr_fun (Module.End.commute_pow_left_of_commute
    (LieSubmodule.Quotient.toEnd_comp_mk' F x) k) m
  simpa using this
/-
**LieModule.posFittingComp_eq_bot_of_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 `LieM
odule`。
形式化陈述：∀ (R : Type u_2) (L : Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [LieModule.IsNilpotent L M], LieModule.posFittingCom
p R L M = ⊥
参数：R : Type u_2；L : Type u_3；M : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LieModule.posFittingCompOf_eq_bot_of_isNilpotent`：∀ (R : Type u_2) {L : 
Type u_3} (M : Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieA
lgebra R L]   [inst_3 : AddCommGroup M…
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma posFittingComp_eq_bot_of_isNilpotent
    [IsNilpotent L M] :
    posFittingComp R L M = ⊥ := by
  simp [posFittingComp]

section map_comap

variable {R L M}
variable
  {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]
  {χ : L → R} (f : M →ₗ⁅R,L⁆ M₂)

/-
**LieModule.map_posFittingComp_le** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：map_posFittingComp_le : (posFittingComp R L M).map f <= posFittingComp R L
 M₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.posFittingComp.eq_1`：∀ (R : Type u_2) (L : Type u_3) (M : Type
 u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst
_3 : AddCommGroup M…
· 使用定理 `LieSubmodule.map_iSup`：map_iSup {ι : Sort*} (N : ι -> LieSubmodule R L M
) : (⨆ i, N i).map f = ⨆ i, (N i).map f
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubmodule.map_le_iff_le_comap`：map_le_iff_le_comap : map f N <= N' ↔ 
N <= comap f N'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `LieModule.toEnd_pow_apply_map`：toEnd_pow_apply_map (m : M) : (toEnd R L 
M₂ x ^ k) (f m) = f ((toEnd R L M x ^ k) m)
-/
lemma map_posFittingComp_le :
    (posFittingComp R L M).map f ≤ posFittingComp R L M₂ := by
  rw [posFittingComp, posFittingComp, LieSubmodule.map_iSup]
  refine iSup_mono fun y ↦ LieSubmodule.map_le_iff_le_comap.mpr fun m hm ↦ ?_
  simp only [mem_posFittingCompOf] at hm
  simp only [LieSubmodule.mem_comap, mem_posFittingCompOf]
  intro k
  obtain ⟨n, hn⟩ := hm k
  use f n
  rw [LieModule.toEnd_pow_apply_map, hn]
/-
**LieModule.map_genWeightSpace_le** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：map_genWeightSpace_le : (genWeightSpace M χ).map f <= genWeightSpace M₂ χ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.map_le_iff_le_comap`：map_le_iff_le_comap : map f N <= N' ↔ 
N <= comap f N'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LieModuleHom.instLinearMapClass`：∀ {R : Type u} {L : Type v} {M : Type w
} {N : Type w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGrou
p M] [inst_3 : AddCom…
· 使用定理 `LieModuleHom.map_lie`：map_lie (f : M ->ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x,
 m⁆ = ⁅x, f m⁆
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieModule.mem_genWeightSpace`：mem_genWeightSpace (χ : L -> R) (m : M) : 
m in genWeightSpace M χ ↔ forall x, exists k : Nat, ((toEnd R L M x - χ x • ↑1) 
^ k) m = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Module.End.commute_pow_left_of_commute`：commute_pow_left_of_commute [Sem
iring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₁₂ : R ->+* R₂} {f : M ->ₛₗ[σ₁₂] M
₂} {g : Module.End R M} {g₂ …
-/
lemma map_genWeightSpace_le :
    (genWeightSpace M χ).map f ≤ genWeightSpace M₂ χ := by
  rw [LieSubmodule.map_le_iff_le_comap]
  intro m hm
  simp only [LieSubmodule.mem_comap, mem_genWeightSpace]
  intro x
  have : (toEnd R L M₂ x - χ x • ↑1) ∘ₗ f = f ∘ₗ (toEnd R L M x - χ x • ↑1) := by
    ext; simp
  obtain ⟨k, h⟩ := (mem_genWeightSpace _ _ _).mp hm x
  refine ⟨k, ?_⟩
  simpa [h] using LinearMap.congr_fun (Module.End.commute_pow_left_of_commute this k) m

variable {f}
/-
**LieModule.comap_genWeightSpace_eq_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `LieM
odule`。
形式化陈述：comap_genWeightSpace_eq_of_injective (hf : Injective f) : (genWeightSpace 
M₂ χ).comap f = genWeightSpace M χ
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LieModuleHom.instLinearMapClass`：∀ {R : Type u} {L : Type v} {M : Type w
} {N : Type w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGrou
p M] [inst_3 : AddCom…
· 使用定理 `LieModuleHom.map_lie`：map_lie (f : M ->ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x,
 m⁆ = ⁅x, f m⁆
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Module.End.commute_pow_left_of_commute`：commute_pow_left_of_commute [Sem
iring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₁₂ : R ->+* R₂} {f : M ->ₛₗ[σ₁₂] M
₂} {g : Module.End R M} {g₂ …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `LieSubmodule.map_le_iff_le_comap`：map_le_iff_le_comap : map f N <= N' ↔ 
N <= comap f N'
· 使用引理 `LieModule.map_genWeightSpace_le`：map_genWeightSpace_le : (genWeightSpace
 M χ).map f <= genWeightSpace M₂ χ
-/
lemma comap_genWeightSpace_eq_of_injective (hf : Injective f) :
    (genWeightSpace M₂ χ).comap f = genWeightSpace M χ := by
  refine le_antisymm (fun m hm ↦ ?_) ?_
  · simp only [LieSubmodule.mem_comap, mem_genWeightSpace] at hm
    simp only [mem_genWeightSpace]
    intro x
    have h : (toEnd R L M₂ x - χ x • ↑1) ∘ₗ f =
             f ∘ₗ (toEnd R L M x - χ x • ↑1) := by ext; simp
    obtain ⟨k, hk⟩ := hm x
    use k
    suffices f (((toEnd R L M x - χ x • ↑1) ^ k) m) = 0 by
      rw [← map_zero f] at this; exact hf this
    simpa [hk] using (LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h k) m).symm
  · rw [← LieSubmodule.map_le_iff_le_comap]
    exact map_genWeightSpace_le f
/-
**LieModule.map_genWeightSpace_eq_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `LieMod
ule`。
形式化陈述：map_genWeightSpace_eq_of_injective (hf : Injective f) : (genWeightSpace M 
χ).map f = genWeightSpace M₂ χ ⊓ f.range
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用引理 `LieModule.map_genWeightSpace_le`：map_genWeightSpace_le : (genWeightSpace
 M χ).map f <= genWeightSpace M₂ χ
· 使用引理 `LieSubmodule.map_le_range`：map_le_range {M' : Type*} [AddCommGroup M'] [
Module R M'] [LieRingModule L M'] (f : M ->ₗ⁅R,L⁆ M') : N.map f <= f.range
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieModule.comap_genWeightSpace_eq_of_injective`：comap_genWeightSpace_eq_
of_injective (hf : Injective f) : (genWeightSpace M₂ χ).comap f = genWeightSpace
 M χ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma map_genWeightSpace_eq_of_injective (hf : Injective f) :
    (genWeightSpace M χ).map f = genWeightSpace M₂ χ ⊓ f.range := by
  refine le_antisymm (le_inf_iff.mpr ⟨map_genWeightSpace_le f, LieSubmodule.map_le_range f⟩) ?_
  rintro - ⟨hm, ⟨m, rfl⟩⟩
  simp only [← comap_genWeightSpace_eq_of_injective hf, LieSubmodule.mem_map,
    LieSubmodule.mem_comap]
  exact ⟨m, hm, rfl⟩
/-
**LieModule.map_genWeightSpace_eq** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：map_genWeightSpace_eq (e : M ≃ₗ⁅R,L⁆ M₂) : (genWeightSpace M χ).map e = ge
nWeightSpace M₂ χ
参数：e : M ≃ₗ⁅R,L⁆ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.map_genWeightSpace_eq_of_injective`：map_genWeightSpace_eq_of_i
njective (hf : Injective f) : (genWeightSpace M χ).map f = genWeightSpace M₂ χ ⊓
 f.range
· 使用定理 `LieModuleEquiv.injective`：injective (e : M ≃ₗ⁅R,L⁆ N) : Function.Injecti
ve e
· 使用定理 `LieModuleEquiv.range_coe`：∀ {R : Type u} {L : Type v} [inst : CommRing R
] [inst_1 : LieRing L] (M : Type u_1) [inst_2 : AddCommGroup M]   [inst_3 : _roo
t_.Module R M]…
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_genWeightSpace_eq (e : M ≃ₗ⁅R,L⁆ M₂) :
    (genWeightSpace M χ).map e = genWeightSpace M₂ χ := by
  simp [map_genWeightSpace_eq_of_injective e.injective]
/-
**LieModule.map_posFittingComp_eq** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：map_posFittingComp_eq (e : M ≃ₗ⁅R,L⁆ M₂) : (posFittingComp R L M).map e = 
posFittingComp R L M₂
参数：e : M ≃ₗ⁅R,L⁆ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `LieModule.map_posFittingComp_le`：map_posFittingComp_le : (posFittingComp
 R L M).map f <= posFittingComp R L M₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.map_comp`：map_comp {M'' : Type*} [AddCommGroup M''] [Module
 R M''] [LieRingModule L M''] {g : M' ->ₗ⁅R,L⁆ M''} : N.map (g.comp f) = (N.map 
f).map g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieSubmodule.map_id`：map_id : N.map LieModuleHom.id = N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LieModuleEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃ₗ⁅R,L⁆ N) : fo
rall x, e (e.symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `LieSubmodule.map_mono`：map_mono (h : N <= N₂) : N.map f <= N₂.map f
-/
lemma map_posFittingComp_eq (e : M ≃ₗ⁅R,L⁆ M₂) :
    (posFittingComp R L M).map e = posFittingComp R L M₂ := by
  refine le_antisymm (map_posFittingComp_le _) ?_
  suffices posFittingComp R L M₂ = ((posFittingComp R L M₂).map (e.symm : M₂ →ₗ⁅R,L⁆ M)).map e by
    rw [this]
    exact LieSubmodule.map_mono (map_posFittingComp_le _)
  rw [← LieSubmodule.map_comp]
  convert! LieSubmodule.map_id
  ext
  simp
/-
**LieModule.posFittingComp_map_incl_sup_of_codisjoint** 是 Mathlib 中的一个引理，位于命名空间 
`LieModule`。
形式化陈述：posFittingComp_map_incl_sup_of_codisjoint [IsNoetherian R M] [IsArtinian R
 M] {N₁ N₂ : LieSubmodule R L M} (h : Codisjoint N₁ N₂) : (posFittingComp R L N₁
).map N₁.incl ⊔ (posFittingComp R L N₂).map N₂.incl = posFittingComp R L M
参数：h : Codisjoint N₁ N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `LieModule.eventually_iInf_lowerCentralSeries_eq`：eventually_iInf_lowerCe
ntralSeries_eq [IsArtinian R M] : forallᶠ l in Filter.atTop, ⨅ k, lowerCentralSe
ries R L M k = lowerCentralSeries R L…
· 使用定理 `LieSubmodule.instIsArtinianSubtypeMem`：∀ {R : Type u} {L : Type v} {M : 
Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [in
st_3 : _root_.Module R M] […
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.instIsNoetherianSubtypeMem`：∀ {R : Type u} {L : Type v} {M 
: Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [
inst_3 : _root_.Module R M] […
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieSubmodule.lowerCentralSeries_map_eq_lcs`：lowerCentralSeries_map_eq_lc
s : (lowerCentralSeries R L N k).map N.incl = N.lcs k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Codisjoint.eq_top`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → a ⊔ b = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma posFittingComp_map_incl_sup_of_codisjoint [IsNoetherian R M] [IsArtinian R M]
    {N₁ N₂ : LieSubmodule R L M} (h : Codisjoint N₁ N₂) :
    (posFittingComp R L N₁).map N₁.incl ⊔ (posFittingComp R L N₂).map N₂.incl =
    posFittingComp R L M := by
  obtain ⟨l, hl⟩ := Filter.eventually_atTop.mp <|
    (eventually_iInf_lowerCentralSeries_eq R L N₁).and <|
    (eventually_iInf_lowerCentralSeries_eq R L N₂).and
    (eventually_iInf_lowerCentralSeries_eq R L M)
  obtain ⟨hl₁, hl₂, hl₃⟩ := hl l (le_refl _)
  simp_rw [← iInf_lowerCentralSeries_eq_posFittingComp, hl₁, hl₂, hl₃,
    LieSubmodule.lowerCentralSeries_map_eq_lcs, ← LieSubmodule.lcs_sup, lowerCentralSeries,
    h.eq_top]
/-
**LieModule.genWeightSpace_genWeightSpaceOf_map_incl** 是 Mathlib 中的一个引理，位于命名空间 `
LieModule`。
形式化陈述：genWeightSpace_genWeightSpaceOf_map_incl (x : L) (χ : L -> R) : (genWeight
Space (genWeightSpaceOf M (χ x) x) χ).map (genWeightSpaceOf M (χ x) x).incl = ge
nWeightSpace M χ
参数：x : L；χ : L -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.map_genWeightSpace_eq_of_injective`：map_genWeightSpace_eq_of_i
njective (hf : Injective f) : (genWeightSpace M χ).map f = genWeightSpace M₂ χ ⊓
 f.range
· 使用定理 `LieSubmodule.injective_incl`：injective_incl : Function.Injective N.incl
· 使用定理 `LieSubmodule.range_incl`：range_incl : N.incl.range = N
· 使用引理 `LieModule.genWeightSpace_le_genWeightSpaceOf`：genWeightSpace_le_genWeigh
tSpaceOf (x : L) (χ : L -> R) : genWeightSpace M χ <= genWeightSpaceOf M (χ x) x
-/
lemma genWeightSpace_genWeightSpaceOf_map_incl (x : L) (χ : L → R) :
    (genWeightSpace (genWeightSpaceOf M (χ x) x) χ).map (genWeightSpaceOf M (χ x) x).incl =
    genWeightSpace M χ := by
  simpa [map_genWeightSpace_eq_of_injective (genWeightSpaceOf M (χ x) x).injective_incl]
    using genWeightSpace_le_genWeightSpaceOf M x χ

end map_comap

section fitting_decomposition

variable [IsNoetherian R M] [IsArtinian R M]

/-
**LieModule.isCompl_genWeightSpaceOf_zero_posFittingCompOf** 是 Mathlib 中的一个引理，位于
命名空间 `LieModule`。
形式化陈述：isCompl_genWeightSpaceOf_zero_posFittingCompOf (x : L) : IsCompl (genWeigh
tSpaceOf M 0 x) (posFittingCompOf R M x)
参数：x : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.coe_genWeightSpaceOf_zero`：coe_genWeightSpaceOf_zero (x : L) :
 ↑(genWeightSpaceOf M (0 : R) x) = ⨆ k, LinearMap.ker (toEnd R L M x ^ k)
· 使用定理 `LieSubmodule.sup_toSubmodule`：sup_toSubmodule : (↑(N ⊔ N') : Submodule R
 M) = (N : Submodule R M) ⊔ (N' : Submodule R M)
· 使用定理 `LinearMap.isCompl_iSup_ker_pow_iInf_range_pow`：isCompl_iSup_ker_pow_iInf
_range_pow [IsNoetherian R M] (f : M ->ₗ[R] M) : IsCompl (⨆ n, LinearMap.ker (f 
^ n)) (⨅ n, LinearMap.range (f ^ n)…
-/
lemma isCompl_genWeightSpaceOf_zero_posFittingCompOf (x : L) :
    IsCompl (genWeightSpaceOf M 0 x) (posFittingCompOf R M x) := by
  simpa only [isCompl_iff, codisjoint_iff, disjoint_iff, ← LieSubmodule.toSubmodule_inj,
    LieSubmodule.sup_toSubmodule, LieSubmodule.inf_toSubmodule,
    LieSubmodule.top_toSubmodule, LieSubmodule.bot_toSubmodule, coe_genWeightSpaceOf_zero] using!
    (toEnd R L M x).isCompl_iSup_ker_pow_iInf_range_pow

/-- This lemma exists only to simplify the proof of
`LieModule.isCompl_genWeightSpace_zero_posFittingComp`. -/
/-
**LieModule.isCompl_genWeightSpace_zero_posFittingComp_aux** 是 Mathlib 中的一个引理，位于
命名空间 `LieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma exists only to simplify the proof of
`LieModule.isCompl_genWeightSpace_zero_posFittingComp`.
-/
private lemma isCompl_genWeightSpace_zero_posFittingComp_aux
    (h : ∀ N < (⊤ : LieSubmodule R L M), IsCompl (genWeightSpace N 0) (posFittingComp R L N)) :
    IsCompl (genWeightSpace M 0) (posFittingComp R L M) := by
  set M₀ := genWeightSpace M (0 : L → R)
  set M₁ := posFittingComp R L M
  rcases forall_or_exists_not (fun (x : L) ↦ genWeightSpaceOf M (0 : R) x = ⊤)
    with h | ⟨x, hx : genWeightSpaceOf M (0 : R) x ≠ ⊤⟩
  · suffices IsNilpotent L M by simp [M₀, M₁, isCompl_top_bot]
    replace h : M₀ = ⊤ := by simpa [M₀, genWeightSpace]
    rw [← LieModule.isNilpotent_of_top_iff' (R := R), ← h]
    infer_instance
  · set M₀ₓ := genWeightSpaceOf M (0 : R) x
    set M₁ₓ := posFittingCompOf R M x
    set M₀ₓ₀ := genWeightSpace M₀ₓ (0 : L → R)
    set M₀ₓ₁ := posFittingComp R L M₀ₓ
    have h₁ : IsCompl M₀ₓ M₁ₓ := isCompl_genWeightSpaceOf_zero_posFittingCompOf R L M x
    have h₂ : IsCompl M₀ₓ₀ M₀ₓ₁ := h M₀ₓ hx.lt_top
    have h₃ : M₀ₓ₀.map M₀ₓ.incl = M₀ := by
      rw [map_genWeightSpace_eq_of_injective M₀ₓ.injective_incl, inf_eq_left,
        LieSubmodule.range_incl]
      exact iInf_le _ x
    have h₄ : M₀ₓ₁.map M₀ₓ.incl ⊔ M₁ₓ = M₁ := by
      apply le_antisymm <| sup_le_iff.mpr
        ⟨map_posFittingComp_le _, posFittingCompOf_le_posFittingComp R L M x⟩
      rw [← posFittingComp_map_incl_sup_of_codisjoint h₁.codisjoint]
      exact sup_le_sup_left LieSubmodule.map_incl_le _
    rw [← h₃, ← h₄]
    apply Disjoint.isCompl_sup_right_of_isCompl_sup_left
    · rw [disjoint_iff, ← LieSubmodule.map_inf M₀ₓ.injective_incl, h₂.inf_eq_bot,
        LieSubmodule.map_bot]
    · rwa [← LieSubmodule.map_sup, h₂.sup_eq_top, LieModuleHom.map_top, LieSubmodule.range_incl]

/-- This is the Fitting decomposition of the Lie module `M`. -/
/-
**LieModule.isCompl_genWeightSpace_zero_posFittingComp** 是 Mathlib 中的一个引理，位于命名空间
 `LieModule`。
形式化陈述：isCompl_genWeightSpace_zero_posFittingComp : IsCompl (genWeightSpace M 0) 
(posFittingComp R L M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `LieSubmodule.wellFoundedLT_of_isArtinian`：wellFoundedLT_of_isArtinian [I
sArtinian R M] : WellFoundedLT (LieSubmodule R L M)
· 使用定理 `_private.Mathlib.Algebra.Lie.Weights.Basic.0.LieModule.isCompl_genWeight
Space_zero_posFittingComp_aux`：∀ (R : Type u_2) (L : Type u_3) (M : Type u_4) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M…
· 使用定理 `LieSubmodule.instIsNoetherianSubtypeMem`：∀ {R : Type u} {L : Type v} {M 
: Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [
inst_3 : _root_.Module R M] […
· 使用定理 `LieSubmodule.instIsArtinianSubtypeMem`：∀ {R : Type u} {L : Type v} {M : 
Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [in
st_3 : _root_.Module R M] […
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LieSubmodule.map_incl_lt_iff_lt_top`：map_incl_lt_iff_lt_top {N' : LieSub
module R L N} : N'.map (LieSubmodule.incl N) < N ↔ N' < ⊤
· 使用定理 `LieSubmodule.injective_incl`：injective_incl : Function.Injective N.incl
· 使用定理 `OrderIso.isCompl_iff`：OrderIso.isCompl_iff {x y : α} : IsCompl x y ↔ IsC
ompl (f x) (f y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieModule.map_posFittingComp_eq`：map_posFittingComp_eq (e : M ≃ₗ⁅R,L⁆ M₂
) : (posFittingComp R L M).map e = posFittingComp R L M₂
· 使用引理 `LieModule.map_genWeightSpace_eq`：map_genWeightSpace_eq (e : M ≃ₗ⁅R,L⁆ M₂
) : (genWeightSpace M χ).map e = genWeightSpace M₂ χ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
This is the Fitting decomposition of the Lie module `M`.
-/
lemma isCompl_genWeightSpace_zero_posFittingComp :
    IsCompl (genWeightSpace M 0) (posFittingComp R L M) := by
  let P : LieSubmodule R L M → Prop := fun N ↦ IsCompl (genWeightSpace N 0) (posFittingComp R L N)
  suffices P ⊤ by
    let e := LieModuleEquiv.ofTop R L M
    rw [← map_genWeightSpace_eq e, ← map_posFittingComp_eq e]
    exact (LieSubmodule.orderIsoMapComap e).isCompl_iff.mp this
  induction (⊤ : LieSubmodule R L M) using
    (LieSubmodule.wellFoundedLT_of_isArtinian R L M).induction with | ind N hN
  refine isCompl_genWeightSpace_zero_posFittingComp_aux R L N fun N' hN' ↦ ?_
  suffices IsCompl (genWeightSpace (N'.map N.incl) 0) (posFittingComp R L (N'.map N.incl)) by
    let e := LieSubmodule.equivMapOfInjective N' N.injective_incl
    rw [← map_genWeightSpace_eq e, ← map_posFittingComp_eq e] at this
    exact (LieSubmodule.orderIsoMapComap e).isCompl_iff.mpr this
  exact hN _ (LieSubmodule.map_incl_lt_iff_lt_top.mpr hN')

end fitting_decomposition

section IsTorsionFree
variable [IsDomain R] [Module.IsTorsionFree R M]

/-
**LieModule.disjoint_genWeightSpaceOf** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：disjoint_genWeightSpaceOf {x : L} {φ₁ φ₂ : R} (h : φ₁ != φ₂) : Disjoint (g
enWeightSpaceOf M φ₁ x) (genWeightSpaceOf M φ₂ x)
参数：h : φ₁ != φ₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.disjoint_toSubmodule`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用引理 `Module.End.disjoint_genEigenspace`：disjoint_genEigenspace [IsDomain R] [
IsTorsionFree R M] (f : End R M) {μ₁ μ₂ : R} (hμ : μ₁ != μ₂) (k l : Nat∞) : Disj
oint (f.genEigenspace μ…
-/
lemma disjoint_genWeightSpaceOf {x : L} {φ₁ φ₂ : R} (h : φ₁ ≠ φ₂) :
    Disjoint (genWeightSpaceOf M φ₁ x) (genWeightSpaceOf M φ₂ x) := by
  rw [← LieSubmodule.disjoint_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact Module.End.disjoint_genEigenspace _ h _ _
/-
**LieModule.disjoint_genWeightSpace** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：disjoint_genWeightSpace {χ₁ χ₂ : L -> R} (h : χ₁ != χ₂) : Disjoint (genWei
ghtSpace M χ₁) (genWeightSpace M χ₂)
参数：h : χ₁ != χ₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用引理 `LieModule.genWeightSpace_le_genWeightSpaceOf`：genWeightSpace_le_genWeigh
tSpaceOf (x : L) (χ : L -> R) : genWeightSpace M χ <= genWeightSpaceOf M (χ x) x
· 使用引理 `LieModule.disjoint_genWeightSpaceOf`：disjoint_genWeightSpaceOf {x : L} {
φ₁ φ₂ : R} (h : φ₁ != φ₂) : Disjoint (genWeightSpaceOf M φ₁ x) (genWeightSpaceOf
 M φ₂ x)
-/
lemma disjoint_genWeightSpace {χ₁ χ₂ : L → R} (h : χ₁ ≠ χ₂) :
    Disjoint (genWeightSpace M χ₁) (genWeightSpace M χ₂) := by
  obtain ⟨x, hx⟩ : ∃ x, χ₁ x ≠ χ₂ x := Function.ne_iff.mp h
  exact (disjoint_genWeightSpaceOf R L M hx).mono
    (genWeightSpace_le_genWeightSpaceOf M x χ₁) (genWeightSpace_le_genWeightSpaceOf M x χ₂)
/-
**LieModule.injOn_genWeightSpace** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：injOn_genWeightSpace : InjOn (fun (χ : L -> R) => genWeightSpace M χ) {χ |
 genWeightSpace M χ != ⊥}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.disjoint_genWeightSpace`：disjoint_genWeightSpace {χ₁ χ₂ : L ->
 R} (h : χ₁ != χ₂) : Disjoint (genWeightSpace M χ₁) (genWeightSpace M χ₂)
-/
lemma injOn_genWeightSpace :
    InjOn (fun (χ : L → R) ↦ genWeightSpace M χ) {χ | genWeightSpace M χ ≠ ⊥} := by
  rintro χ₁ _ χ₂ hχ₂ (hχ₁₂ : genWeightSpace M χ₁ = genWeightSpace M χ₂)
  contrapose! hχ₂
  simpa [hχ₁₂] using disjoint_genWeightSpace R L M hχ₂

/-- Lie module weight spaces are independent.

See also `LieModule.iSupIndep_genWeightSpace'`. -/
/-
**LieModule.iSupIndep_genWeightSpace** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：iSupIndep_genWeightSpace : iSupIndep fun χ : L -> R => genWeightSpace M χ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LieSubmodule.iInf_toSubmodule`：iInf_toSubmodule {ι} (p : ι -> LieSubmodu
le R L M) : (↑(⨅ i, p i) : Submodule R M) = ⨅ i, (p i : Submodule R M)
· 使用引理 `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`：independe
nt_iInf_maxGenEigenspace_of_forall_mapsTo (h : forall i j φ, MapsTo (f i) ((f j)
.maxGenEigenspace φ) ((f j).maxGenEigenspace φ)) : …
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […

--- 原说明 ---
Lie module weight spaces are independent.

See also `LieModule.iSupIndep_genWeightSpace'`.
-/
lemma iSupIndep_genWeightSpace : iSupIndep fun χ : L → R ↦ genWeightSpace M χ := by
  simp only [← LieSubmodule.iSupIndep_toSubmodule, genWeightSpace,
    LieSubmodule.iInf_toSubmodule]
  exact Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (toEnd R L M)
    (fun x y φ z ↦ (genWeightSpaceOf M φ y).lie_mem)
/-
**LieModule.iSupIndep_genWeightSpace'** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：iSupIndep_genWeightSpace' : iSupIndep fun χ : Weight R L M => genWeightSpa
ce M χ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep.comp`：iSupIndep.comp {ι ι' : Sort*} {t : ι -> α} {f : ι' -> ι}
 (ht : iSupIndep t) (hf : Injective f) : iSupIndep (t ∘ f)
· 使用引理 `LieModule.iSupIndep_genWeightSpace`：iSupIndep_genWeightSpace : iSupIndep
 fun χ : L -> R => genWeightSpace M χ
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma iSupIndep_genWeightSpace' : iSupIndep fun χ : Weight R L M ↦ genWeightSpace M χ :=
  (iSupIndep_genWeightSpace R L M).comp <|
    Subtype.val_injective.comp (Weight.equivSetOfPred R L M).injective
/-
**LieModule.iSupIndep_genWeightSpaceOf** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：iSupIndep_genWeightSpaceOf (x : L) : iSupIndep fun (χ : R) => genWeightSpa
ceOf M χ x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.iSupIndep_toSubmodule`：∀ {R : Type u} {L : Type v} {M : Typ
e w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_
3 : _root_.Module R M] […
· 使用定理 `Module.End.independent_genEigenspace`：independent_genEigenspace [IsDomai
n R] [IsTorsionFree R M] (f : End R M) (k : Nat∞) : iSupIndep (f.genEigenspace ·
 k)
-/
lemma iSupIndep_genWeightSpaceOf (x : L) : iSupIndep fun (χ : R) ↦ genWeightSpaceOf M χ x := by
  rw [← LieSubmodule.iSupIndep_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact (toEnd R L M x).independent_genEigenspace _
/-
**LieModule.finite_genWeightSpaceOf_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`
。
形式化陈述：finite_genWeightSpaceOf_ne_bot [IsNoetherian R M] (x : L) : {χ : R | genWe
ightSpaceOf M χ x != ⊥}.Finite
参数：x : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedGT.finite_ne_bot_of_iSupIndep`：WellFoundedGT.finite_ne_bot_of
_iSupIndep [WellFoundedGT α] {ι : Type*} {t : ι -> α} (ht : iSupIndep t) : Set.F
inite {i | t i != ⊥}
· 使用引理 `LieModule.iSupIndep_genWeightSpaceOf`：iSupIndep_genWeightSpaceOf (x : L)
 : iSupIndep fun (χ : R) => genWeightSpaceOf M χ x
-/
lemma finite_genWeightSpaceOf_ne_bot [IsNoetherian R M] (x : L) :
    {χ : R | genWeightSpaceOf M χ x ≠ ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep (iSupIndep_genWeightSpaceOf R L M x)
/-
**LieModule.finite_genWeightSpace_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：finite_genWeightSpace_ne_bot [IsNoetherian R M] : {χ : L -> R | genWeightS
pace M χ != ⊥}.Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedGT.finite_ne_bot_of_iSupIndep`：WellFoundedGT.finite_ne_bot_of
_iSupIndep [WellFoundedGT α] {ι : Type*} {t : ι -> α} (ht : iSupIndep t) : Set.F
inite {i | t i != ⊥}
· 使用引理 `LieModule.iSupIndep_genWeightSpace`：iSupIndep_genWeightSpace : iSupIndep
 fun χ : L -> R => genWeightSpace M χ
-/
lemma finite_genWeightSpace_ne_bot [IsNoetherian R M] :
    {χ : L → R | genWeightSpace M χ ≠ ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep (iSupIndep_genWeightSpace R L M)
/-
**LieModule.Weight.instFinite** 是 Mathlib 中的一个定理，位于命名空间 `LieModule.Weight`。
形式化陈述：∀ (R : Type u_2) (L : Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [inst
_7 : LieRing.IsNilpotent L] [IsDomain R] [Module.IsTorsionFree R M] [IsNoetheria
n R M],   Finite (LieModule.Weight R L M)
参数：R : Type u_2；L : Type u_3；M : Type u_4；LieModule.Weight R L M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.finite_genWeightSpace_ne_bot`：finite_genWeightSpace_ne_bot [Is
Noetherian R M] : {χ : L -> R | genWeightSpace M χ != ⊥}.Finite
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
instance Weight.instFinite [IsNoetherian R M] : Finite (Weight R L M) := by
  have : Finite {χ : L → R | genWeightSpace M χ ≠ ⊥} := finite_genWeightSpace_ne_bot R L M
  exact Finite.of_injective (equivSetOfPred R L M) (equivSetOfPred R L M).injective
/-
**LieModule.Weight.instFintype** 是 Mathlib 中的一个定义，位于命名空间 `LieModule.Weight`。
形式化陈述：(R : Type u_2) →   (L : Type u_3) →     (M : Type u_4) →       [inst : Com
mRing R] →         [inst_1 : LieRing L] →           [inst_2 : LieAlgebra R L] → 
            [inst_3 : AddCommGroup M] →               [inst_4 : _root_.Module R 
M] →                 [inst_5 : LieRingModule L M] →                   [inst_6 : 
LieModule R L M] →                     [inst_7 : LieRing.IsNilpotent L] →       
                [IsDomain R] → [Module.IsTorsionFree R M] → [IsNoetherian R M] →
 Fintype (LieModule.Weight R L M)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.Weight.instFinite`：∀ (R : Type u_2) (L : Type u_3) (M : Type u
_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3
 : AddCommGroup M…
-/
noncomputable instance Weight.instFintype [IsNoetherian R M] : Fintype (Weight R L M) := .ofFinite _

end IsTorsionFree

/-- A Lie module `M` of a Lie algebra `L` is triangularizable if the endomorphism of `M` defined by
any `x : L` is triangularizable. -/
/-
**LieModule.IsTriangularizable** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieModule`。
形式化陈述：(R : Type u_2) →   (L : Type u_3) →     (M : Type u_4) →       [inst : Com
mRing R] →         [inst_1 : LieRing L] →           [inst_2 : LieAlgebra R L] → 
            [inst_3 : AddCommGroup M] →               [inst_4 : _root_.Module R 
M] → [inst_5 : LieRingModule L M] → [LieModule R L M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie module `M` of a Lie algebra `L` is triangularizable if the endomorphism of
 `M` defined by
any `x : L` is triangularizable.
-/
class IsTriangularizable : Prop where
  maxGenEigenspace_eq_top : ∀ x, ⨆ φ, (toEnd R L M x).maxGenEigenspace φ = ⊤
/-
**LieModule.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L' : LieSubalgebra R L) [IsTriangularizable R L M] : IsTriangularizable R L' M where
  maxGenEigenspace_eq_top x := IsTriangularizable.maxGenEigenspace_eq_top (x : L)
/-
**LieModule.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : LieIdeal R L) [IsTriangularizable R L M] : IsTriangularizable R I M where
  maxGenEigenspace_eq_top x := IsTriangularizable.maxGenEigenspace_eq_top (x : L)

attribute [local instance 100] LieRing.ofAssociativeRing
/-
**LieModule.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTriangularizable R L M] : IsTriangularizable R (LieModule.toEnd R L M).range M where
  maxGenEigenspace_eq_top := by
    rintro ⟨-, x, rfl⟩
    exact IsTriangularizable.maxGenEigenspace_eq_top x

omit [LieRing.IsNilpotent L] in
/-
**LieModule.IsTriangularizable.exists_hasEigenvalue** 是 Mathlib 中的一个定理，位于命名空间 `L
ieModule.IsTriangularizable`。
形式化陈述：∀ (R : Type u_2) (L : Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [Nont
rivial M] [LieModule.IsTriangularizable R L M] (x : L), ∃ φ, ((LieModule.toEnd R
 L M) x).HasEigenvalue φ
参数：R : Type u_2；L : Type u_3；M : Type u_4；x : L；(LieModule.toEnd R L M) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.IsTriangularizable.maxGenEigenspace_eq_top`：∀ {R : Type u_2} {
L : Type u_3} {M : Type u_4} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : 
LieAlgebra R L}   {inst_3 : AddCommGroup M…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one`：hasUnifEigenvalu
e_iff_hasUnifEigenvalue_one {f : End R M} {μ : R} {k : Nat∞} (hk : 0 < k) : f.Ha
sUnifEigenvalue μ k ↔ f.HasUnifEigenvalue μ …
· 使用定理 `ENat.top_pos`：top_pos : (0 : Nat∞) < ⊤
-/
lemma IsTriangularizable.exists_hasEigenvalue [Nontrivial M] [IsTriangularizable R L M] (x : L) :
    ∃ φ, (toEnd R L M x).HasEigenvalue φ := by
  suffices ∃ φ, (toEnd R L M x).maxGenEigenspace φ ≠ ⊥ by
    obtain ⟨φ, hφ⟩ := this
    exact ⟨φ, (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one ENat.top_pos).mp hφ⟩
  have := maxGenEigenspace_eq_top (R := R) (L := L) (M := M) x
  contrapose! this
  simp [this]

@[simp]
/-
**LieModule.iSup_genWeightSpaceOf_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：iSup_genWeightSpaceOf_eq_top [IsTriangularizable R L M] (x : L) : ⨆ (φ : R
), genWeightSpaceOf M φ x = ⊤
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.iSup_toSubmodule`：iSup_toSubmodule {ι} (p : ι -> LieSubmodu
le R L M) : (↑(⨆ i, p i) : Submodule R M) = ⨆ i, (p i : Submodule R M)
· 使用定理 `LieSubmodule.top_toSubmodule`：top_toSubmodule : ((⊤ : LieSubmodule R L M
) : Submodule R M) = ⊤
· 使用定理 `LieModule.IsTriangularizable.maxGenEigenspace_eq_top`：∀ {R : Type u_2} {
L : Type u_3} {M : Type u_4} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : 
LieAlgebra R L}   {inst_3 : AddCommGroup M…
-/
lemma iSup_genWeightSpaceOf_eq_top [IsTriangularizable R L M] (x : L) :
    ⨆ (φ : R), genWeightSpaceOf M φ x = ⊤ := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.iSup_toSubmodule,
    LieSubmodule.top_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact IsTriangularizable.maxGenEigenspace_eq_top x

open LinearMap Module in
@[simp]
/-
**LieModule.trace_toEnd_genWeightSpace** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：trace_toEnd_genWeightSpace [IsDomain R] [IsPrincipalIdealRing R] [Module.F
ree R M] [Module.Finite R M] (χ : L -> R) (x : L) : trace R _ (toEnd R L (genWei
ghtSpace M χ) x) = finrank R (genWeightSpace M χ) • χ x
参数：χ : L -> R；x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.algebraMap_end_eq_smul_id`：algebraMap_end_eq_smul_id (a : R) : al
gebraMap R (End S M) a = a • LinearMap.id
· 使用引理 `LieModule.isNilpotent_toEnd_sub_algebraMap`：isNilpotent_toEnd_sub_algebr
aMap [IsNoetherian R M] (χ : L -> R) (x : L) : _root_.IsNilpotent toEnd R L (gen
WeightSpace M χ) x - algebraMap …
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `IsNilpotent.eq_zero`：IsNilpotent.eq_zero [Zero R] [Pow R Nat] [IsReduced
 R] (h : IsNilpotent x) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `LinearMap.isNilpotent_trace_of_isNilpotent`：isNilpotent_trace_of_isNilpo
tent {f : M ->ₗ[R] M} (hf : IsNilpotent f) : IsNilpotent (trace R M f)
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `LinearMap.trace_id`：trace_id : trace R M id = (finrank R M : R)
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `LieSubmodule.instIsNoetherianSubtypeMem`：∀ {R : Type u} {L : Type v} {M 
: Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [
inst_3 : _root_.Module R M] […
· 使用定理 `LieSubmodule.instIsTorsionFreeSubtypeMem`：∀ {R : Type u} {L : Type v} {M
 : Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   
[inst_3 : _root_.Module R M] […
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `Module.instIsReflexiveOfFiniteOfProjective`：∀ (R : Type u_1) (N : Type u
_3) [inst : CommSemiring R] [inst_1 : AddCommMonoid N] [inst_2 : _root_.Module R
 N]   [Module.Finite R N] [Modul…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
lemma trace_toEnd_genWeightSpace [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Free R M] [Module.Finite R M] (χ : L → R) (x : L) :
    trace R _ (toEnd R L (genWeightSpace M χ) x) = finrank R (genWeightSpace M χ) • χ x := by
  suffices _root_.IsNilpotent ((toEnd R L (genWeightSpace M χ) x) - χ x • LinearMap.id) by
    replace this := (isNilpotent_trace_of_isNilpotent this).eq_zero
    rwa [map_sub, map_smul, trace_id, sub_eq_zero, smul_eq_mul, mul_comm,
      ← nsmul_eq_mul] at this
  rw [← Module.algebraMap_end_eq_smul_id]
  exact isNilpotent_toEnd_sub_algebraMap M χ x

section field

open Module

variable (K)
variable [Field K] [LieAlgebra K L] [Module K M] [LieModule K L M] [FiniteDimensional K M]

/-
**LieModule.instIsTriangularizableOfIsAlgClosed** 是 Mathlib 中的一个实例，位于命名空间 `LieMo
dule`。
形式化陈述：instIsTriangularizableOfIsAlgClosed [IsAlgClosed K] : IsTriangularizable K
 L M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.iSup_maxGenEigenspace_eq_top`：iSup_maxGenEigenspace_eq_top [I
sAlgClosed K] [FiniteDimensional K V] (f : End K V) : ⨆ (μ : K), f.maxGenEigensp
ace μ = ⊤
-/
instance instIsTriangularizableOfIsAlgClosed [IsAlgClosed K] : IsTriangularizable K L M :=
  ⟨fun _ ↦ Module.End.iSup_maxGenEigenspace_eq_top _⟩
/-
**LieModule.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (N : LieSubmodule K L M) [IsTriangularizable K L M] : IsTriangularizable K L N := by
  refine ⟨fun y ↦ ?_⟩
  rw [← N.toEnd_restrict_eq_toEnd y]
  exact Module.End.genEigenspace_restrict_eq_top _ (IsTriangularizable.maxGenEigenspace_eq_top y)

/-- For a triangularizable Lie module in finite dimensions, the weight spaces span the entire space.

See also `LieModule.iSup_genWeightSpace_eq_top'`. -/
/-
**LieModule.iSup_genWeightSpace_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：iSup_genWeightSpace_eq_top [IsTriangularizable K L M] : ⨆ χ : L -> K, genW
eightSpace M χ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.iSup_toSubmodule`：iSup_toSubmodule {ι} (p : ι -> LieSubmodu
le R L M) : (↑(⨆ i, p i) : Submodule R M) = ⨆ i, (p i : Submodule R M)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LieSubmodule.iInf_toSubmodule`：iInf_toSubmodule {ι} (p : ι -> LieSubmodu
le R L M) : (↑(⨅ i, p i) : Submodule R M) = ⨅ i, (p i : Submodule R M)
· 使用引理 `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo`：iSup_iInf
_maxGenEigenspace_eq_top_of_forall_mapsTo [FiniteDimensional K M] (f : ι -> End 
K M) (h : forall i j φ, MapsTo (f i) ((f j).maxGenE…
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `LieModule.IsTriangularizable.maxGenEigenspace_eq_top`：∀ {R : Type u_2} {
L : Type u_3} {M : Type u_4} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : 
LieAlgebra R L}   {inst_3 : AddCommGroup M…

--- 原说明 ---
For a triangularizable Lie module in finite dimensions, the weight spaces span t
he entire space.

See also `LieModule.iSup_genWeightSpace_eq_top'`.
-/
lemma iSup_genWeightSpace_eq_top [IsTriangularizable K L M] :
    ⨆ χ : L → K, genWeightSpace M χ = ⊤ := by
  simp only [← LieSubmodule.toSubmodule_inj, LieSubmodule.iSup_toSubmodule,
    LieSubmodule.iInf_toSubmodule, LieSubmodule.top_toSubmodule, genWeightSpace]
  refine Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (toEnd K L M)
    (fun x y φ z ↦ (genWeightSpaceOf M φ y).lie_mem) ?_
  apply IsTriangularizable.maxGenEigenspace_eq_top
/-
**LieModule.iSup_genWeightSpace_eq_top'** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：iSup_genWeightSpace_eq_top' [IsTriangularizable K L M] : ⨆ χ : Weight K L 
M, genWeightSpace M χ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.iSup_genWeightSpace_eq_top`：iSup_genWeightSpace_eq_top [IsTria
ngularizable K L M] : ⨆ χ : L -> K, genWeightSpace M χ = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.iSup_comp`：Equiv.iSup_comp {g : ι' -> α} (e : ι ≃ ι') : ⨆ x, g (e 
x) = ⨆ y, g y
· 使用定理 `iSup_ne_bot_subtype`：iSup_ne_bot_subtype (f : ι -> α) : ⨆ i : { i // f i
 != ⊥ }, f i = ⨆ i, f i
-/
lemma iSup_genWeightSpace_eq_top' [IsTriangularizable K L M] :
    ⨆ χ : Weight K L M, genWeightSpace M χ = ⊤ := by
  have := iSup_genWeightSpace_eq_top K L M
  erw [← iSup_ne_bot_subtype, ← (Weight.equivSetOfPred K L M).iSup_comp] at this
  exact this
/-
**LieModule.eq_iSup_inf_genWeightSpace** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：eq_iSup_inf_genWeightSpace [IsTriangularizable K L M] (N : LieSubmodule K 
L M) : N = ⨆ χ : Weight K L M, N ⊓ genWeightSpace M χ
参数：N : LieSubmodule K L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.map_incl_top`：map_incl_top : (⊤ : LieSubmodule R L N).map N
.incl = N
· 使用引理 `LieModule.iSup_genWeightSpace_eq_top'`：iSup_genWeightSpace_eq_top' [IsTr
iangularizable K L M] : ⨆ χ : Weight K L M, genWeightSpace M χ = ⊤
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `LieSubmodule.instIsNoetherianSubtypeMem`：∀ {R : Type u} {L : Type v} {M 
: Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [
inst_3 : _root_.Module R M] […
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `LieModule.instIsTriangularizableSubtypeMemLieSubmodule`：∀ (K : Type u_1)
 (L : Type u_3) (M : Type u_4) [inst : LieRing L] [inst_1 : AddCommGroup M] [ins
t_2 : LieRingModule L M]   [inst_3 : Field K…
· 使用定理 `LieSubmodule.map_iSup`：map_iSup {ι : Sort*} (N : ι -> LieSubmodule R L M
) : (⨆ i, N i).map f = ⨆ i, (N i).map f
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LieSubmodule.map_mono`：map_mono (h : N <= N₂) : N.map f <= N₂.map f
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用引理 `LieModule.map_genWeightSpace_le`：map_genWeightSpace_le : (genWeightSpace
 M χ).map f <= genWeightSpace M₂ χ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
lemma eq_iSup_inf_genWeightSpace [IsTriangularizable K L M] (N : LieSubmodule K L M) :
    N = ⨆ χ : Weight K L M, N ⊓ genWeightSpace M χ := by
  refine le_antisymm ?_ (iSup_le fun χ ↦ inf_le_left)
  conv_lhs => rw [← N.map_incl_top, ← iSup_genWeightSpace_eq_top' K L N, LieSubmodule.map_iSup]
  refine iSup_le fun χ_N ↦ ?_
  have hN := (LieSubmodule.map_mono (le_top : genWeightSpace N χ_N ≤ ⊤)).trans N.map_incl_top.le
  exact (le_inf hN (map_genWeightSpace_le _)).trans <| by
    by_cases h : genWeightSpace M (χ_N : L → K) = ⊥
    · simp [h]
    · exact le_iSup_of_le ⟨_, h⟩ le_rfl

end field

end LieModule

