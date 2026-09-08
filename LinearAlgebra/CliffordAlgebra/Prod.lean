/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Clifford algebras of a direct sum of two vector spaces

We show that the Clifford algebra of a direct sum is the graded tensor product of the Clifford
algebras, as `CliffordAlgebra.equivProd`.

## Main definitions:

* `CliffordAlgebra.equivProd : CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R] (evenOdd Q₁ ᵍ⊗[R] evenOdd Q₂)`

## TODO

Introduce morphisms and equivalences of graded algebras, and upgrade `CliffordAlgebra.equivProd`
to a graded algebra equivalence.

-/

@[expose] public section

suppress_compilation

variable {R M₁ M₂ N : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N]
variable [Module R M₁] [Module R M₂] [Module R N]
variable (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Qₙ : QuadraticForm R N)

open scoped TensorProduct

namespace CliffordAlgebra


section map_mul_map

variable {Q₁ Q₂ Qₙ}
variable (f₁ : Q₁ →qᵢ Qₙ) (f₂ : Q₂ →qᵢ Qₙ) (hf : ∀ x y, Qₙ.IsOrtho (f₁ x) (f₂ y))
variable (m₁ : CliffordAlgebra Q₁) (m₂ : CliffordAlgebra Q₂)
include hf

/-- If `m₁` and `m₂` are both homogeneous,
and the quadratic spaces `Q₁` and `Q₂` map into
orthogonal subspaces of `Qₙ` (for instance, when `Qₙ = Q₁.prod Q₂`),
then the product of the embedding in `CliffordAlgebra Q` commutes up to a sign factor. -/
nonrec theorem map_mul_map_of_isOrtho_of_mem_evenOdd
    {i₁ i₂ : ZMod 2} (hm₁ : m₁ ∈ evenOdd Q₁ i₁) (hm₂ : m₂ ∈ evenOdd Q₂ i₂) :
    map f₁ m₁ * map f₂ m₂ = (-1 : ℤˣ) ^ (i₂ * i₁) • (map f₂ m₂ * map f₁ m₁) := by
  -- for each variable, induct on powers of `ι`, then on the exponent of each power
  induction hm₁ using Submodule.iSup_induction' with
  | zero => rw [map_zero, zero_mul, mul_zero, smul_zero]
  | add _ _ _ _ ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy, smul_add]
  | mem i₁' m₁' hm₁ =>
    obtain ⟨i₁n, rfl⟩ := i₁'
    dsimp only at *
    induction hm₁ using Submodule.pow_induction_on_left' with
    | algebraMap =>
      rw [AlgHom.commutes, Nat.cast_zero, mul_zero, uzpow_zero, one_smul, Algebra.commutes]
    | add _ _ _ _ _ ihx ihy =>
      rw [map_add, add_mul, mul_add, ihx, ihy, smul_add]
    | mem_mul m₁ hm₁ i x₁ _hx₁ ih₁ =>
      obtain ⟨v₁, rfl⟩ := hm₁
      -- This is the first interesting goal.
      rw [map_mul, mul_assoc, ih₁, mul_smul_comm, map_apply_ι, Nat.cast_succ, mul_add_one,
        uzpow_add, mul_smul, ← mul_assoc, ← mul_assoc, ← smul_mul_assoc ((-1) ^ i₂)]
      clear ih₁
      congr 2
      induction hm₂ using Submodule.iSup_induction' with
      | zero => rw [map_zero, zero_mul, mul_zero, smul_zero]
      | add _ _ _ _ ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy, smul_add]
      | mem i₂' m₂' hm₂ =>
        clear m₂
        obtain ⟨i₂n, rfl⟩ := i₂'
        dsimp only at *
        induction hm₂ using Submodule.pow_induction_on_left' with
        | algebraMap =>
          rw [AlgHom.commutes, Nat.cast_zero, uzpow_zero, one_smul, Algebra.commutes]
        | add _ _ _ _ _ ihx ihy =>
          rw [map_add, add_mul, mul_add, ihx, ihy, smul_add]
        | mem_mul m₂ hm₂ i x₂ _hx₂ ih₂ =>
          obtain ⟨v₂, rfl⟩ := hm₂
          -- This is the second interesting goal.
          rw [map_mul, map_apply_ι, Nat.cast_succ, ← mul_assoc,
            ι_mul_ι_comm_of_isOrtho (hf _ _), neg_mul, mul_assoc, ih₂, mul_smul_comm,
            ← mul_assoc, ← Units.neg_smul, uzpow_add, uzpow_one, mul_neg_one]

/-
**CliffordAlgebra.commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_left** 是 Ma
thlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_left {i₂ : ZMod 2} (hm₁
 : m₁ in evenOdd Q₁ 0) (hm₂ : m₂ in evenOdd Q₂ i₂) : Commute (map f₁ m₁) (map f₂
 m₂)
参数：hm₁ : m₁ in evenOdd Q₁ 0；hm₂ : m₂ in evenOdd Q₂ i₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CliffordAlgebra.map_mul_map_of_isOrtho_of_mem_evenOdd`：∀ {R : Type u_1} 
{M₁ : Type u_2} {M₂ : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : Add
CommGroup M₁]   [inst_2 : AddCommGroup M₂] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `uzpow_zero`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Mo
dule R (Additive ℤˣ)] (s : ℤˣ), s ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_left
    {i₂ : ZMod 2} (hm₁ : m₁ ∈ evenOdd Q₁ 0) (hm₂ : m₂ ∈ evenOdd Q₂ i₂) :
    Commute (map f₁ m₁) (map f₂ m₂) :=
  (map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂).trans <| by simp
/-
**CliffordAlgebra.commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_right** 是 M
athlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_right {i₁ : ZMod 2} (hm
₁ : m₁ in evenOdd Q₁ i₁) (hm₂ : m₂ in evenOdd Q₂ 0) : Commute (map f₁ m₁) (map f
₂ m₂)
参数：hm₁ : m₁ in evenOdd Q₁ i₁；hm₂ : m₂ in evenOdd Q₂ 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CliffordAlgebra.map_mul_map_of_isOrtho_of_mem_evenOdd`：∀ {R : Type u_1} 
{M₁ : Type u_2} {M₂ : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : Add
CommGroup M₁]   [inst_2 : AddCommGroup M₂] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `uzpow_zero`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Mo
dule R (Additive ℤˣ)] (s : ℤˣ), s ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_right
    {i₁ : ZMod 2} (hm₁ : m₁ ∈ evenOdd Q₁ i₁) (hm₂ : m₂ ∈ evenOdd Q₂ 0) :
    Commute (map f₁ m₁) (map f₂ m₂) :=
  (map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂).trans <| by simp
/-
**CliffordAlgebra.map_mul_map_eq_neg_of_isOrtho_of_mem_evenOdd_one** 是 Mathlib 中
的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：map_mul_map_eq_neg_of_isOrtho_of_mem_evenOdd_one (hm₁ : m₁ in evenOdd Q₁ 1
) (hm₂ : m₂ in evenOdd Q₂ 1) : map f₁ m₁ * map f₂ m₂ = -map f₂ m₂ * map f₁ m₁
参数：hm₁ : m₁ in evenOdd Q₁ 1；hm₂ : m₂ in evenOdd Q₂ 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.map_mul_map_of_isOrtho_of_mem_evenOdd`：∀ {R : Type u_1} 
{M₁ : Type u_2} {M₂ : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : Add
CommGroup M₁]   [inst_2 : AddCommGroup M₂] …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `uzpow_one`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Mod
ule R (Additive ℤˣ)] (s : ℤˣ), s ^ 1 = s
· 使用定理 `Units.neg_smul`：Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u
 : Rˣ) (x : M) : -u • x = -(u • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_mul_map_eq_neg_of_isOrtho_of_mem_evenOdd_one
    (hm₁ : m₁ ∈ evenOdd Q₁ 1) (hm₂ : m₂ ∈ evenOdd Q₂ 1) :
    map f₁ m₁ * map f₂ m₂ = -map f₂ m₂ * map f₁ m₁ := by
  simp [map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂]

end map_mul_map

/-- The forward direction of `CliffordAlgebra.prodEquiv`. -/
/-
**CliffordAlgebra.ofProd** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：ofProd : CliffordAlgebra (Q₁.prod Q₂) ->ₐ[R] (evenOdd Q₁ ᵍotimes[R] evenOd
d Q₂)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.ι_mem_evenOdd_one`：ι_mem_evenOdd_one (m : M) : ι Q m in 
evenOdd Q 1

--- 原说明 ---
The forward direction of `CliffordAlgebra.prodEquiv`.
-/
def ofProd : CliffordAlgebra (Q₁.prod Q₂) →ₐ[R] (evenOdd Q₁ ᵍ⊗[R] evenOdd Q₂) :=
  lift _ ⟨
    LinearMap.coprod
      ((GradedTensorProduct.includeLeft (evenOdd Q₁) (evenOdd Q₂)).toLinearMap
          ∘ₗ (evenOdd Q₁ 1).subtype ∘ₗ (ι Q₁).codRestrict _ (ι_mem_evenOdd_one Q₁))
      ((GradedTensorProduct.includeRight (evenOdd Q₁) (evenOdd Q₂)).toLinearMap
          ∘ₗ (evenOdd Q₂ 1).subtype ∘ₗ (ι Q₂).codRestrict _ (ι_mem_evenOdd_one Q₂)),
    fun m => by
      simp_rw [LinearMap.coprod_apply, LinearMap.coe_comp, Function.comp_apply,
        AlgHom.toLinearMap_apply, QuadraticMap.prod_apply, Submodule.coe_subtype,
        GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply, map_add,
        add_mul, mul_add, GradedTensorProduct.algebraMap_def,
        GradedTensorProduct.tmul_one_mul_one_tmul, GradedTensorProduct.tmul_one_mul_coe_tmul,
        GradedTensorProduct.tmul_coe_mul_one_tmul, GradedTensorProduct.tmul_coe_mul_coe_tmul,
        LinearMap.codRestrict_apply, one_mul, uzpow_one, Units.neg_smul, one_smul, ι_sq_scalar,
        mul_one, ← GradedTensorProduct.algebraMap_def, ← GradedTensorProduct.algebraMap_def']
      abel⟩

@[simp]
/-
**CliffordAlgebra.ofProd_** 是 Mathlib 中的一个引理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofProd_ι_mk (m₁ : M₁) (m₂ : M₂) :
    ofProd Q₁ Q₂ (ι _ (m₁, m₂)) = ι Q₁ m₁ ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ ι Q₂ m₂ := by
  rw [ofProd, lift_ι_apply]
  rfl

/-- The reverse direction of `CliffordAlgebra.prodEquiv`. -/
/-
**CliffordAlgebra.toProd** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：toProd : evenOdd Q₁ ᵍotimes[R] evenOdd Q₂ ->ₐ[R] CliffordAlgebra (Q₁.prod 
Q₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reverse direction of `CliffordAlgebra.prodEquiv`.
-/
def toProd : evenOdd Q₁ ᵍ⊗[R] evenOdd Q₂ →ₐ[R] CliffordAlgebra (Q₁.prod Q₂) :=
  GradedTensorProduct.lift _ _
    (CliffordAlgebra.map <| .inl _ _)
    (CliffordAlgebra.map <| .inr _ _)
    fun _i₁ _i₂ x₁ x₂ => map_mul_map_of_isOrtho_of_mem_evenOdd _ _ (QuadraticMap.IsOrtho.inl_inr) _
      _ x₁.prop x₂.prop

@[simp]
/-
**CliffordAlgebra.toProd_** 是 Mathlib 中的一个引理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toProd_ι_tmul_one (m₁ : M₁) : toProd Q₁ Q₂ (ι _ m₁ ᵍ⊗ₜ 1) = ι _ (m₁, 0) := by
  rw [toProd, GradedTensorProduct.lift_tmul, map_one, mul_one, map_apply_ι,
    QuadraticMap.Isometry.inl_apply]

@[simp]
/-
**CliffordAlgebra.toProd_one_tmul_** 是 Mathlib 中的一个引理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toProd_one_tmul_ι (m₂ : M₂) : toProd Q₁ Q₂ (1 ᵍ⊗ₜ ι _ m₂) = ι _ (0, m₂) := by
  rw [toProd, GradedTensorProduct.lift_tmul, map_one, one_mul, map_apply_ι,
    QuadraticMap.Isometry.inr_apply]
/-
**CliffordAlgebra.toProd_comp_ofProd** 是 Mathlib 中的一个引理，位于命名空间 `CliffordAlgebra`
。
形式化陈述：toProd_comp_ofProd : (toProd Q₁ Q₂).comp (ofProd Q₁ Q₂) = AlgHom.id _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `LinearMap.prod_ext`：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl 
_ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f 
= g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CliffordAlgebra.ofProd_ι_mk`：ofProd_ι_mk (m₁ : M₁) (m₂ : M₂) : ofProd Q₁
 Q₂ (ι _ (m₁, m₂)) = ι Q₁ m₁ ᵍotimesₜ 1 + 1 ᵍotimesₜ ι Q₂ m₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用引理 `CliffordAlgebra.toProd_one_tmul_ι`：toProd_one_tmul_ι (m₂ : M₂) : toProd 
Q₁ Q₂ (1 ᵍotimesₜ ι _ m₂) = ι _ (0, m₂)
· 使用引理 `CliffordAlgebra.toProd_ι_tmul_one`：toProd_ι_tmul_one (m₁ : M₁) : toProd 
Q₁ Q₂ (ι _ m₁ ᵍotimesₜ 1) = ι _ (m₁, 0)
· 使用定理 `Prod.mk_zero_zero`：∀ {M : Type u_3} {N : Type u_4} [inst : Zero M] [inst
_1 : Zero N], (0, 0) = 0
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma toProd_comp_ofProd : (toProd Q₁ Q₂).comp (ofProd Q₁ Q₂) = AlgHom.id _ _ := by
  ext m <;> dsimp
  · rw [ofProd_ι_mk, map_add, toProd_one_tmul_ι, toProd_ι_tmul_one, Prod.mk_zero_zero,
      map_zero, add_zero]
  · rw [ofProd_ι_mk, map_add, toProd_one_tmul_ι, toProd_ι_tmul_one, Prod.mk_zero_zero,
      map_zero, zero_add]
/-
**CliffordAlgebra.ofProd_comp_toProd** 是 Mathlib 中的一个引理，位于命名空间 `CliffordAlgebra`
。
形式化陈述：ofProd_comp_toProd : (ofProd Q₁ Q₂).comp (toProd Q₁ Q₂) = AlgHom.id _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `GradedTensorProduct.algHom_ext`：algHom_ext ⦃f g : (𝒜 ᵍotimes[R] ℬ) ->ₐ[R
] C⦄ (ha : f.comp (includeLeft 𝒜 ℬ) = g.comp (includeLeft 𝒜 ℬ)) (hb : f.comp (in
cludeRight 𝒜 ℬ) = g.…
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GradedTensorProduct.includeLeft_apply`：∀ {R : Type u_1} {ι : Type u_2} {
A : Type u_3} {B : Type u_4} [inst : CommSemiring ι] [inst_1 : DecidableEq ι]   
[inst_2 : CommRing R] [inst…
· 使用引理 `CliffordAlgebra.toProd_ι_tmul_one`：toProd_ι_tmul_one (m₁ : M₁) : toProd 
Q₁ Q₂ (ι _ m₁ ᵍotimesₜ 1) = ι _ (m₁, 0)
· 使用引理 `CliffordAlgebra.ofProd_ι_mk`：ofProd_ι_mk (m₁ : M₁) (m₂ : M₂) : ofProd Q₁
 Q₂ (ι _ (m₁, m₂)) = ι Q₁ m₁ ᵍotimesₜ 1 + 1 ᵍotimesₜ ι Q₂ m₂
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
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `GradedTensorProduct.includeRight_apply`：∀ {R : Type u_1} {ι : Type u_2} 
{A : Type u_3} {B : Type u_4} [inst : CommSemiring ι] [inst_1 : DecidableEq ι]  
 [inst_2 : CommRing R] [inst…
· 使用引理 `CliffordAlgebra.toProd_one_tmul_ι`：toProd_one_tmul_ι (m₂ : M₂) : toProd 
Q₁ Q₂ (1 ᵍotimesₜ ι _ m₂) = ι _ (0, m₂)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
-/
lemma ofProd_comp_toProd : (ofProd Q₁ Q₂).comp (toProd Q₁ Q₂) = AlgHom.id _ _ := by
  ext <;> simp

/-- The Clifford algebra over an orthogonal direct sum of quadratic vector spaces is isomorphic
as an algebra to the graded tensor product of the Clifford algebras of each space.

This is `CliffordAlgebra.toProd` and `CliffordAlgebra.ofProd` as an equivalence. -/
@[simps!]
/-
**CliffordAlgebra.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：prodEquiv : CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R] (evenOdd Q₁ ᵍotimes[R] even
Odd Q₂)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CliffordAlgebra.ofProd_comp_toProd`：ofProd_comp_toProd : (ofProd Q₁ Q₂).
comp (toProd Q₁ Q₂) = AlgHom.id _ _
· 使用引理 `CliffordAlgebra.toProd_comp_ofProd`：toProd_comp_ofProd : (toProd Q₁ Q₂).
comp (ofProd Q₁ Q₂) = AlgHom.id _ _

--- 原说明 ---
The Clifford algebra over an orthogonal direct sum of quadratic vector spaces is
 isomorphic
as an algebra to the graded tensor product of the Clifford algebras of each spac
e.

This is `CliffordAlgebra.toProd` and `CliffordAlgebra.ofProd` as an equivalence.
-/
def prodEquiv : CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R] (evenOdd Q₁ ᵍ⊗[R] evenOdd Q₂) :=
  AlgEquiv.ofAlgHom (ofProd Q₁ Q₂) (toProd Q₁ Q₂) (ofProd_comp_toProd _ _) (toProd_comp_ofProd _ _)

end CliffordAlgebra

