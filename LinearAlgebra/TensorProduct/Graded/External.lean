/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Int.Order.Units
public import Mathlib.Data.ZMod.IntUnitsPower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.Algebra.DirectSum.Algebra

/-!
# Graded tensor products over graded algebras

The graded tensor product $A \hat\otimes_R B$ is imbued with a multiplication defined on homogeneous
tensors by:

$$(a \otimes b) \cdot (a' \otimes b') = (-1)^{\deg a' \deg b} (a \cdot a') \otimes (b \cdot b')$$

where $A$ and $B$ are algebras graded by `ℕ`, `ℤ`, or `ZMod 2` (or more generally, any index
that satisfies `Module ι (Additive ℤˣ)`).

The results for internally-graded algebras (via `GradedAlgebra`) are elsewhere, as is the type
`GradedTensorProduct`.

## Main results

* `TensorProduct.gradedComm`: the symmetric braiding operator on the tensor product of
  externally-graded rings.
* `TensorProduct.gradedMul`: the previously-described multiplication on externally-graded rings, as
  a bilinear map.

## Implementation notes

Rather than implementing the multiplication directly as above, we first implement the canonical
non-trivial braiding sending $a \otimes b$ to $(-1)^{\deg a' \deg b} (b \otimes a)$, as the
multiplication follows trivially from this after some point-free nonsense.

## References

* https://math.stackexchange.com/q/202718/1896
* [*Algebra I*, Bourbaki : Chapter III, §4.7, example (2)][bourbaki1989]

-/

@[expose] public section

open scoped TensorProduct DirectSum

variable {R ι : Type*}

namespace TensorProduct

variable [CommSemiring ι] [Module ι (Additive ℤˣ)] [DecidableEq ι]
variable (𝒜 : ι → Type*) (ℬ : ι → Type*)
variable [CommRing R]
variable [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (ℬ i)]
variable [∀ i, Module R (𝒜 i)] [∀ i, Module R (ℬ i)]

-- this helps with performance
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ι × ι) : Module R (𝒜 (Prod.fst i) ⊗[R] ℬ (Prod.snd i)) :=
  TensorProduct.leftModule

open DirectSum (lof)

variable (R)

section gradedComm

local notation "𝒜ℬ" => (fun i : ι × ι => 𝒜 (Prod.fst i) ⊗[R] ℬ (Prod.snd i))
local notation "ℬ𝒜" => (fun i : ι × ι => ℬ (Prod.fst i) ⊗[R] 𝒜 (Prod.snd i))

/-- Auxiliary construction used to build `TensorProduct.gradedComm`.

This operates on direct sums of tensors instead of tensors of direct sums. -/
/-
**TensorProduct.gradedCommAux** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：gradedCommAux : DirectSum _ 𝒜ℬ ->ₗ[R] DirectSum _ ℬ𝒜
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction used to build `TensorProduct.gradedComm`.

This operates on direct sums of tensors instead of tensors of direct sums.
-/
def gradedCommAux : DirectSum _ 𝒜ℬ →ₗ[R] DirectSum _ ℬ𝒜 :=
  DirectSum.toModule R _ _ fun i =>
    have o := DirectSum.lof R _ ℬ𝒜 (i.2, i.1)
    have s : ℤˣ := ((-1 : ℤˣ) ^ (i.1 * i.2 : ι) : ℤˣ)
    (s • o) ∘ₗ (TensorProduct.comm R _ _).toLinearMap

@[simp]
/-
**TensorProduct.gradedCommAux_lof_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`
。
形式化陈述：gradedCommAux_lof_tmul (i j : ι) (a : 𝒜 i) (b : ℬ j) : gradedCommAux R 𝒜 ℬ
 (lof R _ 𝒜ℬ (i, j) (a otimesₜ b)) = (-1 : Intˣ) ^ (j * i) • lof R _ ℬ𝒜 (j, i) (
b otimesₜ a)
参数：i j : ι；a : 𝒜 i；b : ℬ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.gradedCommAux.eq_1`：∀ (R : Type u_1) {ι : Type u_2} [inst 
: CommSemiring ι] [inst_1 : _root_.Module ι (Additive ℤˣ)]   [inst_2 : Decidable
Eq ι] (𝒜 : ι → Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirectSum.toModule_lof`：toModule_lof (i) (x : M i) : toModule R ι N φ (l
of R ι M i x) = φ i x
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gradedCommAux_lof_tmul (i j : ι) (a : 𝒜 i) (b : ℬ j) :
    gradedCommAux R 𝒜 ℬ (lof R _ 𝒜ℬ (i, j) (a ⊗ₜ b)) =
      (-1 : ℤˣ) ^ (j * i) • lof R _ ℬ𝒜 (j, i) (b ⊗ₜ a) := by
  rw [gradedCommAux]
  simp [mul_comm i j]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**TensorProduct.gradedCommAux_comp_gradedCommAux** 是 Mathlib 中的一个定理，位于命名空间 `Tens
orProduct`。
形式化陈述：gradedCommAux_comp_gradedCommAux : gradedCommAux R 𝒜 ℬ ∘ₗ gradedCommAux R 
ℬ 𝒜 = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.linearMap_ext`：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H :
 forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `DirectSum.instIsScalarTower`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `DirectSum.ext`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddComm
Monoid (β i)] {x y : DirectSum ι β},   (∀ (i : ι), x i = y i) → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.gradedCommAux_lof_tmul`：gradedCommAux_lof_tmul (i j : ι) (
a : 𝒜 i) (b : ℬ j) : gradedCommAux R 𝒜 ℬ (lof R _ 𝒜ℬ (i, j) (a otimesₜ b)) = (-1
 : Intˣ) ^ (j * i) • lof R…
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.CompatibleSMul.units`：∀ {M : Type u_8} {M₂ : Type u_10} [inst 
: AddCommGroup M] [inst_1 : AddCommGroup M₂] {R : Type u_14} {S : Type u_15}   [
inst_2 : Monoid R] […
· 使用定理 `LinearMap.CompatibleSMul.intModule`：∀ {M : Type u_8} {M₂ : Type u_10} [i
nst : AddCommGroup M] [inst_1 : AddCommGroup M₂] {S : Type u_14}   [inst_2 : Sem
iring S] [inst_3 : _root…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem gradedCommAux_comp_gradedCommAux :
    gradedCommAux R 𝒜 ℬ ∘ₗ gradedCommAux R ℬ 𝒜 = LinearMap.id := by
  ext i a b
  dsimp
  rw [gradedCommAux_lof_tmul, LinearMap.map_smul_of_tower, gradedCommAux_lof_tmul, smul_smul,
    mul_comm i.2 i.1, Int.units_mul_self, one_smul]

/-- The braiding operation for tensor products of externally `ι`-graded algebras.

This sends $a ⊗ b$ to $(-1)^{\deg a' \deg b} (b ⊗ a)$. -/
/-
**TensorProduct.gradedComm** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：gradedComm : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i) ≃ₗ[R] (⨁ i, ℬ i) otimes[R] (⨁
 i, 𝒜 i)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.gradedCommAux_comp_gradedCommAux`：gradedCommAux_comp_grade
dCommAux : gradedCommAux R 𝒜 ℬ ∘ₗ gradedCommAux R ℬ 𝒜 = LinearMap.id

--- 原说明 ---
The braiding operation for tensor products of externally `ι`-graded algebras.

This sends $a ⊗ b$ to $(-1)^{\deg a' \deg b} (b ⊗ a)$.
-/
def gradedComm :
    (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i) ≃ₗ[R] (⨁ i, ℬ i) ⊗[R] (⨁ i, 𝒜 i) := by
  refine TensorProduct.directSum R R 𝒜 ℬ ≪≫ₗ ?_ ≪≫ₗ (TensorProduct.directSum R R ℬ 𝒜).symm
  exact LinearEquiv.ofLinearMap (gradedCommAux _ _ _) (gradedCommAux _ _ _)
    (gradedCommAux_comp_gradedCommAux _ _ _) (gradedCommAux_comp_gradedCommAux _ _ _)

/-- The braiding is symmetric. -/
@[simp]
/-
**TensorProduct.gradedComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：gradedComm_symm : (gradedComm R 𝒜 ℬ).symm = gradedComm R ℬ 𝒜
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The braiding is symmetric.
-/
theorem gradedComm_symm : (gradedComm R 𝒜 ℬ).symm = gradedComm R ℬ 𝒜 := by
  rfl
/-
**TensorProduct.gradedComm_of_tmul_of** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：gradedComm_of_tmul_of (i j : ι) (a : 𝒜 i) (b : ℬ j) : gradedComm R 𝒜 ℬ (lo
f R _ 𝒜 i a otimesₜ lof R _ ℬ j b) = (-1 : Intˣ) ^ (j * i) • (lof R _ ℬ _ b otim
esₜ lof R _ 𝒜 _ a)
参数：i j : ι；a : 𝒜 i；b : ℬ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.gradedCommAux_comp_gradedCommAux`：gradedCommAux_comp_grade
dCommAux : gradedCommAux R 𝒜 ℬ ∘ₗ gradedCommAux R ℬ 𝒜 = LinearMap.id
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.gradedComm.eq_1`：∀ (R : Type u_1) {ι : Type u_2} [inst : C
ommSemiring ι] [inst_1 : _root_.Module ι (Additive ℤˣ)]   [inst_2 : DecidableEq 
ι] (𝒜 : ι → Type u_…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `TensorProduct.directSum_lof_tmul_lof`：directSum_lof_tmul_lof (i₁ : ι₁) (
m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) : TensorProduct.directSum R S M₁ M₂ (DirectSu
m.lof S ι₁ M₁ i₁ m₁ otimes…
· 使用定理 `TensorProduct.gradedCommAux_lof_tmul`：gradedCommAux_lof_tmul (i j : ι) (
a : 𝒜 i) (b : ℬ j) : gradedCommAux R 𝒜 ℬ (lof R _ 𝒜ℬ (i, j) (a otimesₜ b)) = (-1
 : Intˣ) ^ (j * i) • lof R…
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `LinearEquiv.map_smul`：map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e 
(c • x) = c • e x
· 使用定理 `TensorProduct.directSum_symm_lof_tmul`：directSum_symm_lof_tmul (i₁ : ι₁)
 (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) : (TensorProduct.directSum R S M₁ M₂).symm 
(DirectSum.lof S (ι₁ × ι₂) …
-/
theorem gradedComm_of_tmul_of (i j : ι) (a : 𝒜 i) (b : ℬ j) :
    gradedComm R 𝒜 ℬ (lof R _ 𝒜 i a ⊗ₜ lof R _ ℬ j b) =
      (-1 : ℤˣ) ^ (j * i) • (lof R _ ℬ _ b ⊗ₜ lof R _ 𝒜 _ a) := by
  rw [gradedComm]
  dsimp only [LinearEquiv.trans_apply, LinearEquiv.coe_ofLinearMap]
  rw [TensorProduct.directSum_lof_tmul_lof, gradedCommAux_lof_tmul, Units.smul_def,
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 specialized `map_smul` to `LinearEquiv.map_smul` to avoid timeouts.
    ← Int.cast_smul_eq_zsmul R, LinearEquiv.map_smul, TensorProduct.directSum_symm_lof_tmul,
    Int.cast_smul_eq_zsmul, ← Units.smul_def]
/-
**TensorProduct.gradedComm_tmul_of_zero** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct
`。
形式化陈述：gradedComm_tmul_of_zero (a : ⨁ i, 𝒜 i) (b : ℬ 0) : gradedComm R 𝒜 ℬ (a oti
mesₜ lof R _ ℬ 0 b) = lof R _ ℬ _ b otimesₜ a
参数：a : ⨁ i, 𝒜 i；b : ℬ 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `DirectSum.linearMap_ext`：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H :
 forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.gradedComm_of_tmul_of`：gradedComm_of_tmul_of (i j : ι) (a 
: 𝒜 i) (b : ℬ j) : gradedComm R 𝒜 ℬ (lof R _ 𝒜 i a otimesₜ lof R _ ℬ j b) = (-1 
: Intˣ) ^ (j * i) • (lof …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `uzpow_zero`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Mo
dule R (Additive ℤˣ)] (s : ℤˣ), s ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem gradedComm_tmul_of_zero (a : ⨁ i, 𝒜 i) (b : ℬ 0) :
    gradedComm R 𝒜 ℬ (a ⊗ₜ lof R _ ℬ 0 b) = lof R _ ℬ _ b ⊗ₜ a := by
  suffices
    (gradedComm R 𝒜 ℬ).toLinearMap ∘ₗ
        (TensorProduct.mk R (⨁ i, 𝒜 i) (⨁ i, ℬ i)).flip (lof R _ ℬ 0 b) =
      TensorProduct.mk R _ _ (lof R _ ℬ 0 b) from
    DFunLike.congr_fun this a
  ext i a
  dsimp
  rw [gradedComm_of_tmul_of, zero_mul, uzpow_zero, one_smul]
/-
**TensorProduct.gradedComm_of_zero_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct
`。
形式化陈述：gradedComm_of_zero_tmul (a : 𝒜 0) (b : ⨁ i, ℬ i) : gradedComm R 𝒜 ℬ (lof R
 _ 𝒜 0 a otimesₜ b) = b otimesₜ lof R _ 𝒜 _ a
参数：a : 𝒜 0；b : ⨁ i, ℬ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `DirectSum.linearMap_ext`：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H :
 forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.gradedComm_of_tmul_of`：gradedComm_of_tmul_of (i j : ι) (a 
: 𝒜 i) (b : ℬ j) : gradedComm R 𝒜 ℬ (lof R _ 𝒜 i a otimesₜ lof R _ ℬ j b) = (-1 
: Intˣ) ^ (j * i) • (lof …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `uzpow_zero`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Mo
dule R (Additive ℤˣ)] (s : ℤˣ), s ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem gradedComm_of_zero_tmul (a : 𝒜 0) (b : ⨁ i, ℬ i) :
    gradedComm R 𝒜 ℬ (lof R _ 𝒜 0 a ⊗ₜ b) = b ⊗ₜ lof R _ 𝒜 _ a := by
  suffices
    (gradedComm R 𝒜 ℬ).toLinearMap ∘ₗ (TensorProduct.mk R (⨁ i, 𝒜 i) (⨁ i, ℬ i)) (lof R _ 𝒜 0 a) =
      (TensorProduct.mk R _ _).flip (lof R _ 𝒜 0 a) from
    DFunLike.congr_fun this b
  ext i b
  dsimp
  rw [gradedComm_of_tmul_of, mul_zero, uzpow_zero, one_smul]
/-
**TensorProduct.gradedComm_tmul_one** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：gradedComm_tmul_one [GradedMonoid.GOne ℬ] (a : ⨁ i, 𝒜 i) : gradedComm R 𝒜 
ℬ (a otimesₜ 1) = 1 otimesₜ a
参数：a : ⨁ i, 𝒜 i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.gradedComm_tmul_of_zero`：gradedComm_tmul_of_zero (a : ⨁ i,
 𝒜 i) (b : ℬ 0) : gradedComm R 𝒜 ℬ (a otimesₜ lof R _ ℬ 0 b) = lof R _ ℬ _ b oti
mesₜ a
-/
theorem gradedComm_tmul_one [GradedMonoid.GOne ℬ] (a : ⨁ i, 𝒜 i) :
    gradedComm R 𝒜 ℬ (a ⊗ₜ 1) = 1 ⊗ₜ a :=
  gradedComm_tmul_of_zero _ _ _ _ _
/-
**TensorProduct.gradedComm_one_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：gradedComm_one_tmul [GradedMonoid.GOne 𝒜] (b : ⨁ i, ℬ i) : gradedComm R 𝒜 
ℬ (1 otimesₜ b) = b otimesₜ 1
参数：b : ⨁ i, ℬ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.gradedComm_of_zero_tmul`：gradedComm_of_zero_tmul (a : 𝒜 0)
 (b : ⨁ i, ℬ i) : gradedComm R 𝒜 ℬ (lof R _ 𝒜 0 a otimesₜ b) = b otimesₜ lof R _
 𝒜 _ a
-/
theorem gradedComm_one_tmul [GradedMonoid.GOne 𝒜] (b : ⨁ i, ℬ i) :
    gradedComm R 𝒜 ℬ (1 ⊗ₜ b) = b ⊗ₜ 1 :=
  gradedComm_of_zero_tmul _ _ _ _ _

@[simp]
/-
**TensorProduct.gradedComm_one** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：gradedComm_one [DirectSum.GSemiring 𝒜] [DirectSum.GSemiring ℬ] : gradedCom
m R 𝒜 ℬ 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.gradedComm_one_tmul`：gradedComm_one_tmul [GradedMonoid.GOn
e 𝒜] (b : ⨁ i, ℬ i) : gradedComm R 𝒜 ℬ (1 otimesₜ b) = b otimesₜ 1
-/
theorem gradedComm_one [DirectSum.GSemiring 𝒜] [DirectSum.GSemiring ℬ] : gradedComm R 𝒜 ℬ 1 = 1 :=
  gradedComm_one_tmul _ _ _ _
/-
**TensorProduct.gradedComm_tmul_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `TensorProd
uct`。
形式化陈述：gradedComm_tmul_algebraMap [DirectSum.GSemiring ℬ] [DirectSum.GAlgebra R ℬ
] (a : ⨁ i, 𝒜 i) (r : R) : gradedComm R 𝒜 ℬ (a otimesₜ algebraMap R _ r) = algeb
raMap R _ r otimesₜ a
参数：a : ⨁ i, 𝒜 i；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.gradedComm_tmul_of_zero`：gradedComm_tmul_of_zero (a : ⨁ i,
 𝒜 i) (b : ℬ 0) : gradedComm R 𝒜 ℬ (a otimesₜ lof R _ ℬ 0 b) = lof R _ ℬ _ b oti
mesₜ a
-/
theorem gradedComm_tmul_algebraMap [DirectSum.GSemiring ℬ] [DirectSum.GAlgebra R ℬ]
    (a : ⨁ i, 𝒜 i) (r : R) :
    gradedComm R 𝒜 ℬ (a ⊗ₜ algebraMap R _ r) = algebraMap R _ r ⊗ₜ a :=
  gradedComm_tmul_of_zero _ _ _ _ _
/-
**TensorProduct.gradedComm_algebraMap_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProd
uct`。
形式化陈述：gradedComm_algebraMap_tmul [DirectSum.GSemiring 𝒜] [DirectSum.GAlgebra R 𝒜
] (r : R) (b : ⨁ i, ℬ i) : gradedComm R 𝒜 ℬ (algebraMap R _ r otimesₜ b) = b oti
mesₜ algebraMap R _ r
参数：r : R；b : ⨁ i, ℬ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.gradedComm_of_zero_tmul`：gradedComm_of_zero_tmul (a : 𝒜 0)
 (b : ⨁ i, ℬ i) : gradedComm R 𝒜 ℬ (lof R _ 𝒜 0 a otimesₜ b) = b otimesₜ lof R _
 𝒜 _ a
-/
theorem gradedComm_algebraMap_tmul [DirectSum.GSemiring 𝒜] [DirectSum.GAlgebra R 𝒜]
    (r : R) (b : ⨁ i, ℬ i) :
    gradedComm R 𝒜 ℬ (algebraMap R _ r ⊗ₜ b) = b ⊗ₜ algebraMap R _ r :=
  gradedComm_of_zero_tmul _ _ _ _ _
/-
**TensorProduct.gradedComm_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：gradedComm_algebraMap [DirectSum.GSemiring 𝒜] [DirectSum.GSemiring ℬ] [Dir
ectSum.GAlgebra R 𝒜] [DirectSum.GAlgebra R ℬ] (r : R) : gradedComm R 𝒜 ℬ (algebr
aMap R _ r) = algebraMap R _ r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TensorProduct.gradedComm_algebraMap_tmul`：gradedComm_algebraMap_tmul [Di
rectSum.GSemiring 𝒜] [DirectSum.GAlgebra R 𝒜] (r : R) (b : ⨁ i, ℬ i) : gradedCom
m R 𝒜 ℬ (algebraMap R _ r otim…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.TensorProduct.algebraMap_apply'`：algebraMap_apply' (r : R) : alg
ebraMap R (A otimes[R] B) r = 1 otimesₜ algebraMap R B r
-/
theorem gradedComm_algebraMap [DirectSum.GSemiring 𝒜] [DirectSum.GSemiring ℬ]
    [DirectSum.GAlgebra R 𝒜] [DirectSum.GAlgebra R ℬ] (r : R) :
    gradedComm R 𝒜 ℬ (algebraMap R _ r) = algebraMap R _ r :=
  (gradedComm_algebraMap_tmul R 𝒜 ℬ r 1).trans (Algebra.TensorProduct.algebraMap_apply' r).symm

end gradedComm

variable [DirectSum.GRing 𝒜] [DirectSum.GRing ℬ]
variable [DirectSum.GAlgebra R 𝒜] [DirectSum.GAlgebra R ℬ]

open TensorProduct (assoc map) in
/-- The multiplication operation for tensor products of externally `ι`-graded algebras. -/
noncomputable irreducible_def gradedMul :
    letI AB := DirectSum _ 𝒜 ⊗[R] DirectSum _ ℬ
    letI : Module R AB := TensorProduct.leftModule
    AB →ₗ[R] AB →ₗ[R] AB := by
  refine TensorProduct.curry ?_
  refine map (LinearMap.mul' R (⨁ i, 𝒜 i)) (LinearMap.mul' R (⨁ i, ℬ i)) ∘ₗ ?_
  refine (assoc R _ _ _).symm.toLinearMap ∘ₗ .lTensor _ ?_ ∘ₗ (assoc R _ _ _).toLinearMap
  refine (assoc R _ _ _).toLinearMap ∘ₗ .rTensor _ ?_ ∘ₗ (assoc R _ _ _).symm.toLinearMap
  exact (gradedComm _ _ _).toLinearMap

/-
**TensorProduct.tmul_of_gradedMul_of_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProdu
ct`。
形式化陈述：tmul_of_gradedMul_of_tmul (j₁ i₂ : ι) (a₁ : ⨁ i, 𝒜 i) (b₁ : ℬ j₁) (a₂ : 𝒜 
i₂) (b₂ : ⨁ i, ℬ i) : gradedMul R 𝒜 ℬ (a₁ otimesₜ lof R _ ℬ j₁ b₁) (lof R _ 𝒜 i₂
 a₂ otimesₜ b₂) = (-1 : Intˣ) ^ (j₁ * i₂) • ((a₁ * lof R _ 𝒜 _ a₂) otimesₜ (lof 
R _ ℬ _ b₁ * b₂))
参数：j₁ i₂ : ι；a₁ : ⨁ i, 𝒜 i；b₁ : ℬ j₁；a₂ : 𝒜 i₂；b₂ : ⨁ i, ℬ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.gradedMul_def`：∀ (R : Type u_5) {ι : Type u_6} [inst : Com
mSemiring ι] [inst_1 : _root_.Module ι (Additive ℤˣ)]   [inst_2 : DecidableEq ι]
 (𝒜 : ι → Type u_…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `TensorProduct.gradedComm_of_tmul_of`：gradedComm_of_tmul_of (i j : ι) (a 
: 𝒜 i) (b : ℬ j) : gradedComm R 𝒜 ℬ (lof R _ 𝒜 i a otimesₜ lof R _ ℬ j b) = (-1 
: Intˣ) ^ (j * i) • (lof …
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `LinearEquiv.map_smul`：map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e 
(c • x) = c • e x
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `DirectSum.instIsScalarTower`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
theorem tmul_of_gradedMul_of_tmul (j₁ i₂ : ι)
    (a₁ : ⨁ i, 𝒜 i) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : ⨁ i, ℬ i) :
    gradedMul R 𝒜 ℬ (a₁ ⊗ₜ lof R _ ℬ j₁ b₁) (lof R _ 𝒜 i₂ a₂ ⊗ₜ b₂) =
      (-1 : ℤˣ) ^ (j₁ * i₂) • ((a₁ * lof R _ 𝒜 _ a₂) ⊗ₜ (lof R _ ℬ _ b₁ * b₂)) := by
  rw [gradedMul]
  dsimp only [curry_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, assoc_tmul,
    map_tmul, LinearMap.id_coe, id_eq, assoc_symm_tmul, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul]
  rw [mul_comm j₁ i₂, gradedComm_of_tmul_of]
  -- the tower smul lemmas elaborate too slowly
  rw [Units.smul_def, Units.smul_def, ← Int.cast_smul_eq_zsmul R, ← Int.cast_smul_eq_zsmul R]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_smul` to avoid timeouts.
  rw [← smul_tmul', LinearEquiv.map_smul, tmul_smul, LinearEquiv.map_smul, map_smul]
  dsimp

variable {R}

set_option backward.defeqAttrib.useBackward true in
/-
**TensorProduct.algebraMap_gradedMul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：algebraMap_gradedMul (r : R) (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)) : grade
dMul R 𝒜 ℬ (algebraMap R _ r otimesₜ 1) x = r • x
参数：r : R；x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `DirectSum.instIsScalarTower`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `DirectSum.linearMap_ext`：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H :
 forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.tmul_of_gradedMul_of_tmul`：tmul_of_gradedMul_of_tmul (j₁ i
₂ : ι) (a₁ : ⨁ i, 𝒜 i) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : ⨁ i, ℬ i) : gradedMul R 𝒜 ℬ
 (a₁ otimesₜ lof R _ ℬ j₁ b₁)…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `uzpow_zero`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Mo
dule R (Additive ℤˣ)] (s : ℤˣ), s ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem algebraMap_gradedMul (r : R) (x : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ (algebraMap R _ r ⊗ₜ 1) x = r • x := by
  suffices gradedMul R 𝒜 ℬ (algebraMap R _ r ⊗ₜ 1) = DistribSMul.toLinearMap R _ r by
    exact DFunLike.congr_fun this x
  ext ia a ib b
  dsimp
  erw [tmul_of_gradedMul_of_tmul]
  rw [zero_mul, uzpow_zero, one_smul, smul_tmul']
  erw [one_mul, _root_.Algebra.smul_def]
/-
**TensorProduct.one_gradedMul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：one_gradedMul (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)) : gradedMul R 𝒜 ℬ 1 x 
= x
参数：x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `TensorProduct.algebraMap_gradedMul`：algebraMap_gradedMul (r : R) (x : (⨁
 i, 𝒜 i) otimes[R] (⨁ i, ℬ i)) : gradedMul R 𝒜 ℬ (algebraMap R _ r otimesₜ 1) x 
= r • x
-/
theorem one_gradedMul (x : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ 1 x = x := by
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_one` to avoid timeouts.
  simpa only [RingHom.map_one, one_smul] using! algebraMap_gradedMul 𝒜 ℬ 1 x

set_option backward.defeqAttrib.useBackward true in
/-
**TensorProduct.gradedMul_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：gradedMul_algebraMap (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)) (r : R) : grade
dMul R 𝒜 ℬ x (algebraMap R _ r otimesₜ 1) = r • x
参数：x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `DirectSum.instIsScalarTower`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `DirectSum.linearMap_ext`：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H :
 forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.tmul_of_gradedMul_of_tmul`：tmul_of_gradedMul_of_tmul (j₁ i
₂ : ι) (a₁ : ⨁ i, 𝒜 i) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : ⨁ i, ℬ i) : gradedMul R 𝒜 ℬ
 (a₁ otimesₜ lof R _ ℬ j₁ b₁)…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `uzpow_zero`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Mo
dule R (Additive ℤˣ)] (s : ℤˣ), s ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem gradedMul_algebraMap (x : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) (r : R) :
    gradedMul R 𝒜 ℬ x (algebraMap R _ r ⊗ₜ 1) = r • x := by
  suffices (gradedMul R 𝒜 ℬ).flip (algebraMap R _ r ⊗ₜ 1) = DistribSMul.toLinearMap R _ r by
    exact DFunLike.congr_fun this x
  ext
  dsimp
  erw [tmul_of_gradedMul_of_tmul]
  rw [mul_zero, uzpow_zero, one_smul, smul_tmul',
      mul_one, _root_.Algebra.smul_def, Algebra.commutes]
  rfl
/-
**TensorProduct.gradedMul_one** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：gradedMul_one (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)) : gradedMul R 𝒜 ℬ x 1 
= x
参数：x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `TensorProduct.gradedMul_algebraMap`：gradedMul_algebraMap (x : (⨁ i, 𝒜 i)
 otimes[R] (⨁ i, ℬ i)) (r : R) : gradedMul R 𝒜 ℬ x (algebraMap R _ r otimesₜ 1) 
= r • x
-/
theorem gradedMul_one (x : (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ x 1 = x := by
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_one` to avoid timeouts.
  simpa only [RingHom.map_one, one_smul] using! gradedMul_algebraMap 𝒜 ℬ x 1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**TensorProduct.gradedMul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：gradedMul_assoc (x y z : DirectSum _ 𝒜 otimes[R] DirectSum _ ℬ) : gradedMu
l R 𝒜 ℬ (gradedMul R 𝒜 ℬ x y) z = gradedMul R 𝒜 ℬ x (gradedMul R 𝒜 ℬ y z)
参数：x y z : DirectSum _ 𝒜 otimes[R] DirectSum _ ℬ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `DirectSum.instIsScalarTower`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `DirectSum.linearMap_ext`：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H :
 forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.tmul_of_gradedMul_of_tmul`：tmul_of_gradedMul_of_tmul (j₁ i
₂ : ι) (a₁ : ⨁ i, 𝒜 i) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : ⨁ i, ℬ i) : gradedMul R 𝒜 ℬ
 (a₁ otimesₜ lof R _ ℬ j₁ b₁)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `LinearMap.map_smul₂`：map_smul₂ (f : M₂ ->ₗ[R] N₂ ->ₛₗ[σ₁₂] P₂) (r : R) (
x y) : f (r • x) y = r • f x y
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `DirectSum.of_mul_of`：of_mul_of {i j} (a : A i) (b : A j) : of A i a * of
 A j b = of _ (i + j) (GradedMonoid.GMul.mul a b)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `_private.Mathlib.LinearAlgebra.TensorProduct.Graded.External.0.TensorPro
duct.gradedMul_assoc._abel_1_4`：∀ {ι : Type u_1} [inst : CommSemiring ι] (ixb iy
a iyb iza : ι),   ixb * iya + (ixb * iza + iyb * iza) = iyb * iza + (ixb * iya +
 ixb * iza)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem gradedMul_assoc (x y z : DirectSum _ 𝒜 ⊗[R] DirectSum _ ℬ) :
    gradedMul R 𝒜 ℬ (gradedMul R 𝒜 ℬ x y) z = gradedMul R 𝒜 ℬ x (gradedMul R 𝒜 ℬ y z) := by
  let mA := gradedMul R 𝒜 ℬ
    -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mA ∘ₗ mA =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mA.flip ∘ₗ mA).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext ixa xa ixb xb iya ya iyb yb iza za izb zb
  dsimp [mA]
  simp_rw [tmul_of_gradedMul_of_tmul, Units.smul_def, ← Int.cast_smul_eq_zsmul R,
    LinearMap.map_smul₂, map_smul, DirectSum.lof_eq_of, DirectSum.of_mul_of,
    ← DirectSum.lof_eq_of R, tmul_of_gradedMul_of_tmul, DirectSum.lof_eq_of, ← DirectSum.of_mul_of,
    ← DirectSum.lof_eq_of R, mul_assoc]
  simp_rw [Int.cast_smul_eq_zsmul R, ← Units.smul_def, smul_smul, ← uzpow_add, add_mul, mul_add]
  congr 2
  abel

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**TensorProduct.gradedComm_gradedMul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：gradedComm_gradedMul (x y : DirectSum _ 𝒜 otimes[R] DirectSum _ ℬ) : grade
dComm R 𝒜 ℬ (gradedMul R 𝒜 ℬ x y) = gradedMul R ℬ 𝒜 (gradedComm R 𝒜 ℬ x) (graded
Comm R 𝒜 ℬ y)
参数：x y : DirectSum _ 𝒜 otimes[R] DirectSum _ ℬ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `DirectSum.instIsScalarTower`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `DirectSum.linearMap_ext`：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H :
 forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.gradedComm_of_tmul_of`：gradedComm_of_tmul_of (i j : ι) (a 
: 𝒜 i) (b : ℬ j) : gradedComm R 𝒜 ℬ (lof R _ 𝒜 i a otimesₜ lof R _ ℬ j b) = (-1 
: Intˣ) ^ (j * i) • (lof …
· 使用定理 `TensorProduct.tmul_of_gradedMul_of_tmul`：tmul_of_gradedMul_of_tmul (j₁ i
₂ : ι) (a₁ : ⨁ i, 𝒜 i) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : ⨁ i, ℬ i) : gradedMul R 𝒜 ℬ
 (a₁ otimesₜ lof R _ ℬ j₁ b₁)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.map_smul`：map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e 
(c • x) = c • e x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `DirectSum.of_mul_of`：of_mul_of {i j} (a : A i) (b : A j) : of A i a * of
 A j b = of _ (i + j) (GradedMonoid.GMul.mul a b)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Mathlib.Tactic.Abel.subst_into_add`：subst_into_add {α} [AddCommMonoid α]
 (l r tl tr t) (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r =
 t
· 使用定理 `Mathlib.Tactic.Abel.term_atom`：term_atom {α} [AddCommMonoid α] (x : α) :
 x = term 1 x 0
· 使用定理 `Mathlib.Tactic.Abel.term_add_const`：term_add_const {α} [AddCommMonoid α]
 (n x a k a') (h : a + k = a') : @term α _ n x a + k = term n x a'
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Abel.const_add_term`：const_add_term {α} [AddCommMonoid α]
 (k n x a a') (h : k + a = a') : k + @term α _ n x a = term n x a'
（共 42 条，此处仅展示前 30 条）
-/
theorem gradedComm_gradedMul (x y : DirectSum _ 𝒜 ⊗[R] DirectSum _ ℬ) :
    gradedComm R 𝒜 ℬ (gradedMul R 𝒜 ℬ x y)
      = gradedMul R ℬ 𝒜 (gradedComm R 𝒜 ℬ x) (gradedComm R 𝒜 ℬ y) := by
  suffices (gradedMul R 𝒜 ℬ).compr₂ (gradedComm R 𝒜 ℬ).toLinearMap
      = (gradedMul R ℬ 𝒜 ∘ₗ (gradedComm R 𝒜 ℬ).toLinearMap).compl₂
        (gradedComm R 𝒜 ℬ).toLinearMap from
    LinearMap.congr_fun₂ this x y
  ext i₁ a₁ j₁ b₁ i₂ a₂ j₂ b₂
  dsimp
  rw [gradedComm_of_tmul_of, gradedComm_of_tmul_of, tmul_of_gradedMul_of_tmul]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_smul` to avoid timeouts.
  simp_rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R, LinearEquiv.map_smul, map_smul,
    LinearMap.smul_apply]
  simp_rw [Int.cast_smul_eq_zsmul R, ← Units.smul_def, DirectSum.lof_eq_of, DirectSum.of_mul_of,
    ← DirectSum.lof_eq_of R, gradedComm_of_tmul_of, tmul_of_gradedMul_of_tmul, smul_smul,
    DirectSum.lof_eq_of, ← DirectSum.of_mul_of, ← DirectSum.lof_eq_of R]
  simp_rw [← uzpow_add, mul_add, add_mul, mul_comm i₁ j₂]
  congr 1
  abel_nf
  rw [two_nsmul, uzpow_add, uzpow_add, Int.units_mul_self, one_mul]

end TensorProduct

