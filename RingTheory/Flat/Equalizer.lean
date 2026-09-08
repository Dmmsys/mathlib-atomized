/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.SnakeLemma

/-!
# Base change along flat modules preserves equalizers

We show that base change along flat modules (resp. algebras)
preserves kernels and equalizers.

-/

@[expose] public section

universe t u

noncomputable section

open TensorProduct

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

section Module

variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable {N P : Type*} [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P]
  (f g : N →ₗ[R] P)

/-
**Module.Flat.ker_lTensor_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.Flat.ker_lTensor_eq [Module.Flat R M] : LinearMap.ker (AlgebraTenso
rModule.lTensor S M f) = LinearMap.range (AlgebraTensorModule.lTensor S M (Linea
rMap.ker f).subtype)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用引理 `Module.Flat.lTensor_exact`：lTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄ [
AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] 
[Module R N''] …
· 使用引理 `LinearMap.exact_subtype_ker_map`：exact_subtype_ker_map (g : N ->ₗ[R] P) 
: Exact (Submodule.subtype (ker g)) g
-/
lemma Module.Flat.ker_lTensor_eq [Module.Flat R M] :
    LinearMap.ker (AlgebraTensorModule.lTensor S M f) =
      LinearMap.range (AlgebraTensorModule.lTensor S M (LinearMap.ker f).subtype) := by
  rw [← LinearMap.exact_iff]
  exact Module.Flat.lTensor_exact M (LinearMap.exact_subtype_ker_map f)
/-
**Module.Flat.eqLocus_lTensor_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.Flat.eqLocus_lTensor_eq [Module.Flat R M] : LinearMap.eqLocus (Alge
braTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S M g) = LinearMap.r
ange (AlgebraTensorModule.lTensor S M (LinearMap.eqLocus f g).subtype)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.eqLocus_eq_ker_sub`：eqLocus_eq_ker_sub (f g : M ->ₛₗ[τ₁₂] M₂) 
: eqLocus f g = ker (f - g)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `Module.Flat.ker_lTensor_eq`：Module.Flat.ker_lTensor_eq [Module.Flat R M]
 : LinearMap.ker (AlgebraTensorModule.lTensor S M f) = LinearMap.range (AlgebraT
ensorModule.lTen…
-/
lemma Module.Flat.eqLocus_lTensor_eq [Module.Flat R M] :
    LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f)
      (AlgebraTensorModule.lTensor S M g) =
      LinearMap.range (AlgebraTensorModule.lTensor S M (LinearMap.eqLocus f g).subtype) := by
  rw [LinearMap.eqLocus_eq_ker_sub, LinearMap.eqLocus_eq_ker_sub]
  rw [← map_sub, ker_lTensor_eq]

/-- The bilinear map corresponding to `LinearMap.tensorEqLocus`. -/
/-
**LinearMap.tensorEqLocusBil** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.tensorEqLocusBil : M ->ₗ[S] LinearMap.eqLocus f g ->ₗ[R] LinearM
ap.eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S M 
g) where toFun m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bilinear map corresponding to `LinearMap.tensorEqLocus`.
-/
def LinearMap.tensorEqLocusBil :
    M →ₗ[S] LinearMap.eqLocus f g →ₗ[R]
      LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f)
        (AlgebraTensorModule.lTensor S M g) where
  toFun m :=
    { toFun := fun a ↦ ⟨m ⊗ₜ a, by simp [show f a = g a from a.property]⟩
      map_add' := fun x y ↦ by simp [tmul_add]
      map_smul' := fun r x ↦ by simp }
  map_add' x y := by
    ext
    simp [add_tmul]
  map_smul' r x := by
    ext
    simp [smul_tmul']

/-- The bilinear map corresponding to `LinearMap.tensorKer`. -/
/-
**LinearMap.tensorKerBil** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.tensorKerBil : M ->ₗ[S] LinearMap.ker f ->ₗ[R] LinearMap.ker (Al
gebraTensorModule.lTensor S M f) where toFun m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bilinear map corresponding to `LinearMap.tensorKer`.
-/
def LinearMap.tensorKerBil :
    M →ₗ[S] LinearMap.ker f →ₗ[R] LinearMap.ker (AlgebraTensorModule.lTensor S M f) where
  toFun m :=
    { toFun := fun a ↦ ⟨m ⊗ₜ a, by simp⟩
      map_add' := fun x y ↦ by simp [tmul_add]
      map_smul' := fun r x ↦ by simp }
  map_add' x y := by ext; simp [add_tmul]
  map_smul' r x := by ext y; simp [smul_tmul']

/-- The canonical map `M ⊗[R] eq(f, g) →ₗ[R] eq(𝟙 ⊗ f, 𝟙 ⊗ g)`. -/
/-
**LinearMap.tensorEqLocus** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.tensorEqLocus : M otimes[R] (LinearMap.eqLocus f g) ->ₗ[S] Linea
rMap.eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S 
M g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `M ⊗[R] eq(f, g) →ₗ[R] eq(𝟙 ⊗ f, 𝟙 ⊗ g)`.
-/
def LinearMap.tensorEqLocus : M ⊗[R] (LinearMap.eqLocus f g) →ₗ[S]
    LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S M g) :=
  AlgebraTensorModule.lift (tensorEqLocusBil S M f g)

/-- The canonical map `M ⊗[R] ker f →ₗ[R] ker (𝟙 ⊗ f)`. -/
/-
**LinearMap.tensorKer** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.tensorKer : M otimes[R] (LinearMap.ker f) ->ₗ[S] LinearMap.ker (
AlgebraTensorModule.lTensor S M f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `M ⊗[R] ker f →ₗ[R] ker (𝟙 ⊗ f)`.
-/
def LinearMap.tensorKer : M ⊗[R] (LinearMap.ker f) →ₗ[S]
    LinearMap.ker (AlgebraTensorModule.lTensor S M f) :=
  AlgebraTensorModule.lift (f.tensorKerBil S M)

@[simp]
/-
**LinearMap.tensorKer_tmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.tensorKer_tmul (m : M) (x : LinearMap.ker f) : (tensorKer S M f 
(m otimesₜ[R] x) : M otimes[R] N) = m otimesₜ[R] (x : N)
参数：m : M；x : LinearMap.ker f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
lemma LinearMap.tensorKer_tmul (m : M) (x : LinearMap.ker f) :
    (tensorKer S M f (m ⊗ₜ[R] x) : M ⊗[R] N) = m ⊗ₜ[R] (x : N) :=
  rfl

@[simp]
/-
**LinearMap.tensorKer_coe** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.tensorKer_coe (x : M otimes[R] (LinearMap.ker f)) : (tensorKer S
 M f x : M otimes[R] N) = (ker f).subtype.lTensor M x
参数：x : M otimes[R] (LinearMap.ker f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
lemma LinearMap.tensorKer_coe (x : M ⊗[R] (LinearMap.ker f)) :
    (tensorKer S M f x : M ⊗[R] N) = (ker f).subtype.lTensor M x := by
  induction x <;> simp_all

@[simp]
/-
**LinearMap.tensorEqLocus_tmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.tensorEqLocus_tmul (m : M) (x : LinearMap.eqLocus f g) : (tensor
EqLocus S M f g (m otimesₜ[R] x) : M otimes[R] N) = m otimesₜ[R] (x : N)
参数：m : M；x : LinearMap.eqLocus f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
lemma LinearMap.tensorEqLocus_tmul (m : M) (x : LinearMap.eqLocus f g) :
    (tensorEqLocus S M f g (m ⊗ₜ[R] x) : M ⊗[R] N) = m ⊗ₜ[R] (x : N) :=
  rfl

@[simp]
/-
**LinearMap.tensorEqLocus_coe** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.tensorEqLocus_coe (x : M otimes[R] (LinearMap.eqLocus f g)) : (t
ensorEqLocus S M f g x : M otimes[R] N) = (eqLocus f g).subtype.lTensor M x
参数：x : M otimes[R] (LinearMap.eqLocus f g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
lemma LinearMap.tensorEqLocus_coe (x : M ⊗[R] (LinearMap.eqLocus f g)) :
    (tensorEqLocus S M f g x : M ⊗[R] N) = (eqLocus f g).subtype.lTensor M x := by
  induction x <;> simp_all

/-- (Implementation): Inverse for `LinearMap.tensorKerEquiv`. -/
/-
**LinearMap.tensorKerInv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.tensorKerInv [Module.Flat R M] : ker (AlgebraTensorModule.lTenso
r S M f) ->ₗ[S] M otimes[R] (ker f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation): Inverse for `LinearMap.tensorKerEquiv`.
-/
def LinearMap.tensorKerInv [Module.Flat R M] :
    ker (AlgebraTensorModule.lTensor S M f) →ₗ[S] M ⊗[R] (ker f) :=
  LinearMap.codRestrictOfInjective (LinearMap.ker (AlgebraTensorModule.lTensor S M f)).subtype
    (AlgebraTensorModule.lTensor S M (ker f).subtype)
    (Module.Flat.lTensor_preserves_injective_linearMap (ker f).subtype
      (ker f).injective_subtype) (by simp [Module.Flat.ker_lTensor_eq])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**LinearMap.lTensor_ker_subtype_tensorKerInv** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma LinearMap.lTensor_ker_subtype_tensorKerInv [Module.Flat R M]
    (x : ker (AlgebraTensorModule.lTensor S M f)) :
    (lTensor M (ker f).subtype) ((tensorKerInv S M f) x) = x := by
  rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  simp [LinearMap.tensorKerInv]

/-- (Implementation): Inverse for `LinearMap.tensorEqLocusEquiv`. -/
/-
**LinearMap.tensorEqLocusInv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.tensorEqLocusInv [Module.Flat R M] : eqLocus (AlgebraTensorModul
e.lTensor S M f) (AlgebraTensorModule.lTensor S M g) ->ₗ[S] M otimes[R] (eqLocus
 f g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation): Inverse for `LinearMap.tensorEqLocusEquiv`.
-/
def LinearMap.tensorEqLocusInv [Module.Flat R M] :
    eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S M g) →ₗ[S]
      M ⊗[R] (eqLocus f g) :=
  LinearMap.codRestrictOfInjective
    (LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f)
      (AlgebraTensorModule.lTensor S M g)).subtype
    (AlgebraTensorModule.lTensor S M (eqLocus f g).subtype)
    (Module.Flat.lTensor_preserves_injective_linearMap (eqLocus f g).subtype
      (eqLocus f g).injective_subtype) (by simp [Module.Flat.eqLocus_lTensor_eq])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**LinearMap.lTensor_eqLocus_subtype_tensorEqLocusInv** 是 Mathlib 中的一个引理，位于命名空间 `
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma LinearMap.lTensor_eqLocus_subtype_tensorEqLocusInv [Module.Flat R M]
    (x : eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S M g)) :
    (lTensor M (eqLocus f g).subtype) (tensorEqLocusInv S M f g x) = x := by
  rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  simp [LinearMap.tensorEqLocusInv]

/-- If `M` is `R`-flat, the canonical map `M ⊗[R] ker f →ₗ[R] ker (𝟙 ⊗ f)` is an isomorphism. -/
/-
**LinearMap.tensorKerEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.tensorKerEquiv [Module.Flat R M] : M otimes[R] LinearMap.ker f ≃
ₗ[S] LinearMap.ker (AlgebraTensorModule.lTensor S M f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is `R`-flat, the canonical map `M ⊗[R] ker f →ₗ[R] ker (𝟙 ⊗ f)` is an iso
morphism.
-/
def LinearMap.tensorKerEquiv [Module.Flat R M] :
    M ⊗[R] LinearMap.ker f ≃ₗ[S] LinearMap.ker (AlgebraTensorModule.lTensor S M f) :=
  LinearEquiv.ofLinearMap (LinearMap.tensorKer S M f) (LinearMap.tensorKerInv S M f)
    (by ext x; simp)
    (by
      ext m x
      apply (Module.Flat.lTensor_preserves_injective_linearMap (ker f).subtype
        (ker f).injective_subtype)
      simp)

@[simp]
/-
**LinearMap.tensorKerEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.tensorKerEquiv_apply [Module.Flat R M] (x : M otimes[R] ker f) :
 tensorKerEquiv S M f x = tensorKer S M f x
参数：x : M otimes[R] ker f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
lemma LinearMap.tensorKerEquiv_apply [Module.Flat R M] (x : M ⊗[R] ker f) :
    tensorKerEquiv S M f x = tensorKer S M f x :=
  rfl

@[simp]
/-
**LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm [Module.Flat R M] (x : k
er (AlgebraTensorModule.lTensor S M f)) : (lTensor M (ker f).subtype) ((tensorKe
rEquiv S M f).symm x) = x
参数：x : ker (AlgebraTensorModule.lTensor S M f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `_private.Mathlib.RingTheory.Flat.Equalizer.0.LinearMap.lTensor_ker_subty
pe_tensorKerInv`：∀ {R : Type u_1} (S : Type u_2) [inst : CommRing R] [inst_1 : C
ommRing S] [inst_2 : Algebra R S] (M : Type u_3)   [inst_3 : AddCommGroup M] …
-/
lemma LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm [Module.Flat R M]
    (x : ker (AlgebraTensorModule.lTensor S M f)) :
    (lTensor M (ker f).subtype) ((tensorKerEquiv S M f).symm x) = x :=
  lTensor_ker_subtype_tensorKerInv S M f x

/-- If `M` is `R`-flat, the canonical map `M ⊗[R] eq(f, g) →ₗ[S] eq (𝟙 ⊗ f, 𝟙 ⊗ g)` is an
isomorphism. -/
/-
**LinearMap.tensorEqLocusEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.tensorEqLocusEquiv [Module.Flat R M] : M otimes[R] eqLocus f g ≃
ₗ[S] eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S 
M g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is `R`-flat, the canonical map `M ⊗[R] eq(f, g) →ₗ[S] eq (𝟙 ⊗ f, 𝟙 ⊗ g)` 
is an
isomorphism.
-/
def LinearMap.tensorEqLocusEquiv [Module.Flat R M] :
    M ⊗[R] eqLocus f g ≃ₗ[S]
      eqLocus (AlgebraTensorModule.lTensor S M f)
        (AlgebraTensorModule.lTensor S M g) :=
  LinearEquiv.ofLinearMap (LinearMap.tensorEqLocus S M f g) (LinearMap.tensorEqLocusInv S M f g)
    (by ext; simp)
    (by
      ext m x
      apply (Module.Flat.lTensor_preserves_injective_linearMap (eqLocus f g).subtype
        (eqLocus f g).injective_subtype)
      simp)

@[simp]
/-
**LinearMap.tensorEqLocusEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.tensorEqLocusEquiv_apply [Module.Flat R M] (x : M otimes[R] Line
arMap.eqLocus f g) : LinearMap.tensorEqLocusEquiv S M f g x = LinearMap.tensorEq
Locus S M f g x
参数：x : M otimes[R] LinearMap.eqLocus f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
lemma LinearMap.tensorEqLocusEquiv_apply [Module.Flat R M] (x : M ⊗[R] LinearMap.eqLocus f g) :
    LinearMap.tensorEqLocusEquiv S M f g x = LinearMap.tensorEqLocus S M f g x :=
  rfl

@[simp]
/-
**LinearMap.lTensor_eqLocus_subtype_tensoreqLocusEquiv_symm** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：LinearMap.lTensor_eqLocus_subtype_tensoreqLocusEquiv_symm [Module.Flat R M
] (x : eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor 
S M g)) : (lTensor M (eqLocus f g).subtype) ((tensorEqLocusEquiv S M f g).symm x
) = x
参数：x : eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor 
S M g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `_private.Mathlib.RingTheory.Flat.Equalizer.0.LinearMap.lTensor_eqLocus_s
ubtype_tensorEqLocusInv`：∀ {R : Type u_1} (S : Type u_2) [inst : CommRing R] [in
st_1 : CommRing S] [inst_2 : Algebra R S] (M : Type u_3)   [inst_3 : AddCommGrou
p M] …
-/
lemma LinearMap.lTensor_eqLocus_subtype_tensoreqLocusEquiv_symm [Module.Flat R M]
    (x : eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S M g)) :
    (lTensor M (eqLocus f g).subtype) ((tensorEqLocusEquiv S M f g).symm x) = x :=
  lTensor_eqLocus_subtype_tensorEqLocusInv S M f g x

variable {M}

/--
Given a short exact sequence `0 → M → N → P → 0` with `P` flat,
then any `A ⊗ M → A ⊗ N` is injective.
-/
/-
**LinearMap.lTensor_injective_of_exact_of_flat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.lTensor_injective_of_exact_of_flat [Module.Flat R P] (f : N ->ₗ[
R] P) (hf : Function.Surjective f) (g : M ->ₗ[R] N) (hg : Function.Injective g) 
(H : Function.Exact g f) (A : Type*) [AddCommGroup A] [Module R A] : Function.In
jective (g.lTensor A)
参数：f : N ->ₗ[R] P；hf : Function.Surjective f；g : M ->ₗ[R] N；hg : Function.Inject
ive g；H : Function.Exact g f；A : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.linearCombination_surjective`：linearCombination_surjective (h : 
Function.Surjective v) : Function.Surjective (linearCombination R v)
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用定理 `lTensor_exact`：lTensor_exact : Exact (lTensor Q f) (lTensor Q g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.lTensor_comp_rTensor`：lTensor_comp_rTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (g.lTensor P).comp (f.rTensor N) = map f g
· 使用定理 `LinearMap.rTensor_comp_lTensor`：rTensor_comp_lTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (f.rTensor Q).comp (g.lTensor M) = map f g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
· 使用定理 `rTensor_exact`：rTensor_exact : Exact (rTensor Q f) (rTensor Q g)
· 使用引理 `LinearMap.exact_subtype_ker_map`：exact_subtype_ker_map (g : N ->ₗ[R] P) 
: Exact (Submodule.subtype (ker g)) g
· 使用定理 `LinearMap.lTensor_surjective`：LinearMap.lTensor_surjective (hg : Functio
n.Surjective g) : Function.Surjective (lTensor Q g)
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `SnakeLemma.exact_δ'_left`：∀ {R : Type u_1} [inst : CommRing R] {M₁ : Typ
e u_2} {M₂ : Type u_3} {M₃ : Type u_4} {N₁ : Type u_5} {N₂ : Type u_6}   {N₃ : T
ype u_7} [inst…
· 使用定理 `LinearMap.rTensor_surjective`：LinearMap.rTensor_surjective (hg : Functio
n.Surjective g) : Function.Surjective (rTensor Q g)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}

--- 原说明 ---
Given a short exact sequence `0 → M → N → P → 0` with `P` flat,
then any `A ⊗ M → A ⊗ N` is injective.
-/
lemma LinearMap.lTensor_injective_of_exact_of_flat [Module.Flat R P]
    (f : N →ₗ[R] P) (hf : Function.Surjective f) (g : M →ₗ[R] N) (hg : Function.Injective g)
    (H : Function.Exact g f) (A : Type*) [AddCommGroup A] [Module R A] :
    Function.Injective (g.lTensor A) := by
/-
The proof is taking a resolution `0 → K → Q → A → 0` with `Q` flat,
and applying snake lemma on the following diagram to
```
                      0
                      ↓
    K ⊗ M → K ⊗ N → K ⊗ P → 0
      ↓       ↓       ↓
0 → Q ⊗ M → Q ⊗ N → Q ⊗ P
      ↓       ↓
    A ⊗ M → A ⊗ N
      ↓       ↓
      0       0
```
to get `0 → A ⊗ K → A ⊗ M` exact.
-/
  let Q := A →₀ R
  let π : Q →ₗ[R] A := Finsupp.linearCombination R fun a ↦ a
  have hπ : Function.Surjective π := Finsupp.linearCombination_surjective _ Function.surjective_id
  let K := LinearMap.ker π
  have := SnakeLemma.exact_δ'_left (K.subtype.rTensor M) (K.subtype.rTensor N) (K.subtype.rTensor P)
    (g.lTensor K) (f.lTensor K) (lTensor_exact K H hf) (g.lTensor Q) (f.lTensor Q)
    (lTensor_exact Q H hf) (by simp) (by simp) (K₃ := Unit) 0
    (by simpa using Module.Flat.rTensor_preserves_injective_linearMap _ K.subtype_injective)
    (π.rTensor M) (rTensor_exact _ (exact_subtype_ker_map π) hπ) (π.rTensor N)
    (rTensor_exact _ (exact_subtype_ker_map π) hπ) (lTensor_surjective K hf)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hg) (g.lTensor A)
    (by simp) (rTensor_surjective _ hπ)
  rw [Subsingleton.elim (SnakeLemma.δ' ..) 0] at this
  simpa using this

/-- Given surjection `f : N → P` with `P` flat, then `A ⊗ ker f ≃ ker (A ⊗ f)`.
Also see `LinearMap.tensorKerEquiv` for the version with `A` flat instead. -/
/-
**LinearMap.kerLTensorEquivOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.kerLTensorEquivOfSurjective [Module.Flat R P] (f : N ->ₗ[R] P) (
hf : Function.Surjective f) (A : Type*) [AddCommGroup A] [Module R A] : LinearMa
p.ker (f.lTensor A) ≃ₗ[R] A otimes[R] LinearMap.ker f
参数：f : N ->ₗ[R] P；hf : Function.Surjective f；A : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given surjection `f : N → P` with `P` flat, then `A ⊗ ker f ≃ ker (A ⊗ f)`.
Also see `LinearMap.tensorKerEquiv` for the version with `A` flat instead.
-/
def LinearMap.kerLTensorEquivOfSurjective [Module.Flat R P]
    (f : N →ₗ[R] P) (hf : Function.Surjective f) (A : Type*) [AddCommGroup A] [Module R A] :
    LinearMap.ker (f.lTensor A) ≃ₗ[R] A ⊗[R] LinearMap.ker f := by
  refine .ofEq _ _ ?_ ≪≫ₗ (LinearEquiv.ofInjective _ (LinearMap.lTensor_injective_of_exact_of_flat
    f hf _ (LinearMap.ker f).subtype_injective (LinearMap.exact_subtype_ker_map _) _)).symm
  rw [LinearMap.exact_iff.mp (lTensor_exact _ (LinearMap.exact_subtype_ker_map _) hf)]

@[simp]
/-
**LinearMap.tensorKerEquivOfSurjective_symm_tmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.tensorKerEquivOfSurjective_symm_tmul [Module.Flat R P] (f : N ->
ₗ[R] P) (hf : Function.Surjective f) (A : Type*) [AddCommGroup A] [Module R A] (
a y) : ((f.kerLTensorEquivOfSurjective hf A).symm (a otimesₜ y)).1 = a otimesₜ y
.1
参数：f : N ->ₗ[R] P；hf : Function.Surjective f；A : Type*；a y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LinearMap.tensorKerEquivOfSurjective_symm_tmul [Module.Flat R P]
    (f : N →ₗ[R] P) (hf : Function.Surjective f) (A : Type*) [AddCommGroup A] [Module R A] (a y) :
    ((f.kerLTensorEquivOfSurjective hf A).symm (a ⊗ₜ y)).1 = a ⊗ₜ y.1 := rfl

end Module

section Algebra

variable (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (f g : A →ₐ[R] B)

/-- (Implementation): Use `AlgHom.tensorEqualizer` instead. -/
/-
**AlgHom.tensorEqualizerAux** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.tensorEqualizerAux : T otimes[R] AlgHom.equalizer f g ->ₗ[S] AlgHom
.equalizer (Algebra.TensorProduct.map (AlgHom.id S T) f) (Algebra.TensorProduct.
map (AlgHom.id S T) g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation): Use `AlgHom.tensorEqualizer` instead.
-/
def AlgHom.tensorEqualizerAux :
    T ⊗[R] AlgHom.equalizer f g →ₗ[S]
      AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S T) f)
        (Algebra.TensorProduct.map (AlgHom.id S T) g) :=
  LinearMap.tensorEqLocus S T (f : A →ₗ[R] B) (g : A →ₗ[R] B)

private local instance : AddHomClass (A →ₐ[R] B) A B := inferInstance

@[simp]
/-
**AlgHom.coe_tensorEqualizerAux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma AlgHom.coe_tensorEqualizerAux (x : T ⊗[R] AlgHom.equalizer f g) :
    (AlgHom.tensorEqualizerAux S T f g x : T ⊗[R] A) =
      Algebra.TensorProduct.map (AlgHom.id S T) (AlgHom.equalizer f g).val x := by
  induction x with
  | zero => rfl
  | tmul => rfl
  | add x y hx hy => simp [hx, hy]
/-
**AlgHom.tensorEqualizerAux_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgHom.tensorEqualizerAux_mul (x y : T otimes[R] AlgHom.equalizer f g) : A
lgHom.tensorEqualizerAux S T f g (x * y) = AlgHom.tensorEqualizerAux S T f g x *
 AlgHom.tensorEqualizerAux S T f g y
参数：x y : T otimes[R] AlgHom.equalizer f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.RingTheory.Flat.Equalizer.0.AlgHom.coe_tensorEqualizerA
ux`：∀ {R : Type u_1} (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : Algebra R S] (T : Type u_3)   [inst_3 : CommRing T] [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma AlgHom.tensorEqualizerAux_mul (x y : T ⊗[R] AlgHom.equalizer f g) :
    AlgHom.tensorEqualizerAux S T f g (x * y) =
      AlgHom.tensorEqualizerAux S T f g x *
        AlgHom.tensorEqualizerAux S T f g y := by
  apply Subtype.ext
  rw [AlgHom.coe_tensorEqualizerAux]
  simp

/-- The canonical map `T ⊗[R] eq(f, g) →ₐ[S] eq (𝟙 ⊗ f, 𝟙 ⊗ g)`. -/
/-
**AlgHom.tensorEqualizer** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.tensorEqualizer : T otimes[R] AlgHom.equalizer f g ->ₐ[S] AlgHom.eq
ualizer (Algebra.TensorProduct.map (AlgHom.id S T) f) (Algebra.TensorProduct.map
 (AlgHom.id S T) g)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgHom.tensorEqualizerAux_mul`：AlgHom.tensorEqualizerAux_mul (x y : T ot
imes[R] AlgHom.equalizer f g) : AlgHom.tensorEqualizerAux S T f g (x * y) = AlgH
om.tensorEqualizerA…

--- 原说明 ---
The canonical map `T ⊗[R] eq(f, g) →ₐ[S] eq (𝟙 ⊗ f, 𝟙 ⊗ g)`.
-/
def AlgHom.tensorEqualizer :
    T ⊗[R] AlgHom.equalizer f g →ₐ[S]
      AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S T) f)
        (Algebra.TensorProduct.map (AlgHom.id S T) g) :=
  AlgHom.ofLinearMap (AlgHom.tensorEqualizerAux S T f g)
    rfl (AlgHom.tensorEqualizerAux_mul S T f g)

@[simp]
/-
**AlgHom.coe_tensorEqualizer** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgHom.coe_tensorEqualizer (x : T otimes[R] AlgHom.equalizer f g) : (AlgHo
m.tensorEqualizer S T f g x : T otimes[R] A) = Algebra.TensorProduct.map (AlgHom
.id S T) (AlgHom.equalizer f g).val x
参数：x : T otimes[R] AlgHom.equalizer f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.Flat.Equalizer.0.AlgHom.coe_tensorEqualizerA
ux`：∀ {R : Type u_1} (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : Algebra R S] (T : Type u_3)   [inst_3 : CommRing T] [ins…
-/
lemma AlgHom.coe_tensorEqualizer (x : T ⊗[R] AlgHom.equalizer f g) :
    (AlgHom.tensorEqualizer S T f g x : T ⊗[R] A) =
      Algebra.TensorProduct.map (AlgHom.id S T) (AlgHom.equalizer f g).val x :=
  AlgHom.coe_tensorEqualizerAux S T f g x

/-- If `T` is `R`-flat, the canonical map
`T ⊗[R] eq(f, g) →ₐ[S] eq (𝟙 ⊗ f, 𝟙 ⊗ g)` is an isomorphism. -/
/-
**AlgHom.tensorEqualizerEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.tensorEqualizerEquiv [Module.Flat R T] : T otimes[R] AlgHom.equaliz
er f g ≃ₐ[S] AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S T) f) (Alg
ebra.TensorProduct.map (AlgHom.id S T) g)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgHom.tensorEqualizerAux_mul`：AlgHom.tensorEqualizerAux_mul (x y : T ot
imes[R] AlgHom.equalizer f g) : AlgHom.tensorEqualizerAux S T f g (x * y) = AlgH
om.tensorEqualizerA…

--- 原说明 ---
If `T` is `R`-flat, the canonical map
`T ⊗[R] eq(f, g) →ₐ[S] eq (𝟙 ⊗ f, 𝟙 ⊗ g)` is an isomorphism.
-/
def AlgHom.tensorEqualizerEquiv [Module.Flat R T] :
    T ⊗[R] AlgHom.equalizer f g ≃ₐ[S]
      AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S T) f)
        (Algebra.TensorProduct.map (AlgHom.id S T) g) :=
  AlgEquiv.ofLinearEquiv (LinearMap.tensorEqLocusEquiv S T f.toLinearMap g.toLinearMap)
    rfl (AlgHom.tensorEqualizerAux_mul S T f g)

@[simp]
/-
**AlgHom.tensorEqualizerEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgHom.tensorEqualizerEquiv_apply [Module.Flat R T] (x : T otimes[R] AlgHo
m.equalizer f g) : AlgHom.tensorEqualizerEquiv S T f g x = AlgHom.tensorEqualize
r S T f g x
参数：x : T otimes[R] AlgHom.equalizer f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma AlgHom.tensorEqualizerEquiv_apply [Module.Flat R T]
    (x : T ⊗[R] AlgHom.equalizer f g) :
    AlgHom.tensorEqualizerEquiv S T f g x = AlgHom.tensorEqualizer S T f g x :=
  rfl

variable (R A) in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
Given a surjection of `R`-algebras `S → T` with kernel `I`, such that `T` is flat,
the kernel of the map `A ⊗ S → A ⊗ T` is the base change of `I` along `S → A ⊗ S`.
-/
/-
**Algebra.kerTensorProductMapIdToAlgHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Algebra.kerTensorProductMapIdToAlgHomEquiv [Module.Flat R T] (h₁ : Functio
n.Surjective (algebraMap S T)) : RingHom.ker (Algebra.TensorProduct.map (.id A A
) (IsScalarTower.toAlgHom R S T)) ≃ₗ[A otimes[R] S] (A otimes[R] S) otimes[S] (R
ingHom.ker (algebraMap S T))
参数：h₁ : Function.Surjective (algebraMap S T)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a surjection of `R`-algebras `S → T` with kernel `I`, such that `T` is fla
t,
the kernel of the map `A ⊗ S → A ⊗ T` is the base change of `I` along `S → A ⊗ S
`.
-/
def Algebra.kerTensorProductMapIdToAlgHomEquiv
    [Module.Flat R T] (h₁ : Function.Surjective (algebraMap S T)) :
    RingHom.ker (Algebra.TensorProduct.map (.id A A) (IsScalarTower.toAlgHom R S T)) ≃ₗ[A ⊗[R] S]
      (A ⊗[R] S) ⊗[S] (RingHom.ker (algebraMap S T)) := by
  let φ : A ⊗[R] S →ₐ[A] A ⊗[R] T :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  let ePp : A ⊗[R] S ≃ₐ[S] S ⊗[R] A :=
    { __ := Algebra.TensorProduct.comm _ _ _, commutes' _ := rfl }
  let e₃ : (RingHom.ker φ) ≃ₗ[R] A ⊗[R] (RingHom.ker (algebraMap S T)) :=
    (LinearMap.kerLTensorEquivOfSurjective (IsScalarTower.toAlgHom R S T).toLinearMap
      h₁ A).restrictScalars R
  let e₄' : (RingHom.ker φ) ≃ₗ[R] (A ⊗[R] S) ⊗[S] (RingHom.ker (algebraMap S T)) :=
    e₃ ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange _ _ S _ _).symm.restrictScalars R ≪≫ₗ
      (AlgebraTensorModule.congr (.refl S _) ePp.symm.toLinearEquiv).restrictScalars R ≪≫ₗ
      (_root_.TensorProduct.comm _ _ _).restrictScalars R
  let e₄ : (A ⊗[R] S) ⊗[S] (RingHom.ker (algebraMap S T)) ≃ₗ[A ⊗[R] S] (RingHom.ker φ) :=
    { __ := e₄'.symm, map_smul' r' x := by
        dsimp
        induction x with
        | zero => simp only [smul_zero, LinearEquiv.map_zero]
        | add x y _ _ => simp only [smul_add, LinearEquiv.map_add, *]
        | tmul x y =>
        induction x with
        | zero => simp only [zero_tmul, smul_zero, LinearEquiv.map_zero]
        | add x y _ _ => simp only [smul_add, add_tmul, LinearEquiv.map_add, *]
        | tmul x z =>
        induction r' with
        | zero => simp only [zero_smul, LinearEquiv.map_zero]
        | add x y _ _ => simp only [add_smul, LinearEquiv.map_add, *]
        | tmul r s =>
        rw [smul_tmul']
        ext1
        dsimp [e₄', ePp, φ]
        change ((r * x) ⊗ₜ[R] ((s * z) * y.1)) = (r ⊗ₜ[R] s) * (x ⊗ₜ[R] (z * y.1))
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_assoc] }
  exact e₄.symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
/-
**Algebra.kerTensorProductMapIdToAlgHomEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：Algebra.kerTensorProductMapIdToAlgHomEquiv_symm_apply [Module.Flat R T] (h
₁ : Function.Surjective (algebraMap S T)) (x y z) : ((kerTensorProductMapIdToAlg
HomEquiv R S T A h₁).symm ((x otimesₜ y) otimesₜ z)).1 = x otimesₜ (y * z.1)
参数：h₁ : Function.Surjective (algebraMap S T)；x y z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma Algebra.kerTensorProductMapIdToAlgHomEquiv_symm_apply [Module.Flat R T]
    (h₁ : Function.Surjective (algebraMap S T)) (x y z) :
    ((kerTensorProductMapIdToAlgHomEquiv R S T A h₁).symm ((x ⊗ₜ y) ⊗ₜ z)).1 =
      x ⊗ₜ (y * z.1) := rfl

end Algebra

namespace RingHom

/--
A property `P` of ring homomorphisms is said to have stable equalizers, if the equalizer
of algebra maps between algebras with structure morphisms satisfying `P`, is preserved by
arbitrary base change.
-/
/-
**RingHom.HasStableEqualizers** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：HasStableEqualizers (P : forall {R S : Type u} [CommRing R] [CommRing S], 
(R ->+* S) -> Prop) : Prop
参数：P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `P` of ring homomorphisms is said to have stable equalizers, if the e
qualizer
of algebra maps between algebras with structure morphisms satisfying `P`, is pre
served by
arbitrary base change.
-/
def HasStableEqualizers (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra R B]
    (f g : A →ₐ[R] B), P (algebraMap R A) → P (algebraMap R B) →
    Function.Bijective (f.tensorEqualizer R S g)

end RingHom

