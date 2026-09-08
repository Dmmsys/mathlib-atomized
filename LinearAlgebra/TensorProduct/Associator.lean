/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Associators and unitors for tensor products of modules over a commutative ring.

-/

@[expose] public section

variable {R : Type*} [CommSemiring R]
variable {R' : Type*} [Monoid R']
variable {R'' : Type*} [Semiring R'']
variable {A M N P Q S T : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [AddCommMonoid Q] [AddCommMonoid S] [AddCommMonoid T]
variable [Module R M] [Module R N] [Module R Q] [Module R S] [Module R T]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable (M N)

namespace TensorProduct

variable [Module R P]

variable {M N}

section

variable (R M)

/-- The base ring is a left identity for the tensor product of modules, up to linear equivalence.
-/
/-
**TensorProduct.lid** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：(R : Type u_1) →   [inst : CommSemiring R] →     (M : Type u_5) → [inst_1 
: AddCommMonoid M] → [inst_2 : _root_.Module R M] → TensorProduct R R M ≃ₗ[R] M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base ring is a left identity for the tensor product of modules, up to linear
 equivalence.
-/
protected def lid : R ⊗[R] M ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap
    (lift <| LinearMap.lsmul R M)
    (mk R R M 1)
    (LinearMap.ext fun _ => by simp)
    (ext' fun r m => by simp [← tmul_smul, ← smul_tmul, smul_eq_mul, mul_one])

end

@[simp]
/-
**TensorProduct.lid_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：lid_tmul (m : M) (r : R) : (TensorProduct.lid R M : R otimes M -> M) (r ot
imesₜ m) = r • m
参数：m : M；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lid_tmul (m : M) (r : R) : (TensorProduct.lid R M : R ⊗ M → M) (r ⊗ₜ m) = r • m :=
  rfl

@[simp]
/-
**TensorProduct.lid_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：lid_symm_apply (m : M) : (TensorProduct.lid R M).symm m = 1 otimesₜ m
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lid_symm_apply (m : M) : (TensorProduct.lid R M).symm m = 1 ⊗ₜ m :=
  rfl
/-
**TensorProduct.toLinearMap_symm_lid** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：toLinearMap_symm_lid : (TensorProduct.lid R M).symm.toLinearMap = mk R R M
 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_symm_lid : (TensorProduct.lid R M).symm.toLinearMap = mk R R M 1 := rfl
/-
**TensorProduct.includeRight_lid** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：includeRight_lid {S : Type*} [Semiring S] [Algebra R S] (m : R otimes[R] M
) : (1 : S) otimesₜ[R] (TensorProduct.lid R M) m = (LinearMap.rTensor M (Algebra
.algHom R R S).toLinearMap) m
参数：m : R otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
lemma includeRight_lid {S : Type*} [Semiring S] [Algebra R S] (m : R ⊗[R] M) :
    (1 : S) ⊗ₜ[R] (TensorProduct.lid R M) m =
      (LinearMap.rTensor M (Algebra.algHom R R S).toLinearMap) m := by
  suffices ∀ m, (LinearMap.rTensor M (Algebra.algHom R R S).toLinearMap).comp
    (TensorProduct.lid R M).symm.toLinearMap m = 1 ⊗ₜ[R] m by
    simp [← this]
  intros; simp

section

variable (R M)

/-- The base ring is a right identity for the tensor product of modules, up to linear equivalence.
-/
/-
**TensorProduct.rid** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：(R : Type u_1) →   [inst : CommSemiring R] →     (M : Type u_5) → [inst_1 
: AddCommMonoid M] → [inst_2 : _root_.Module R M] → TensorProduct R M R ≃ₗ[R] M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base ring is a right identity for the tensor product of modules, up to linea
r equivalence.
-/
protected def rid : M ⊗[R] R ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap
    (lift <| .flip (LinearMap.lsmul R M))
    (mk R M R |>.flip 1)
    (LinearMap.ext <| one_smul _)
    (ext <| by ext; simp)

end

@[simp]
/-
**TensorProduct.rid_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：rid_tmul (m : M) (r : R) : (TensorProduct.rid R M) (m otimesₜ r) = r • m
参数：m : M；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rid_tmul (m : M) (r : R) : (TensorProduct.rid R M) (m ⊗ₜ r) = r • m :=
  rfl

@[simp]
/-
**TensorProduct.rid_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：rid_symm_apply (m : M) : (TensorProduct.rid R M).symm m = m otimesₜ 1
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rid_symm_apply (m : M) : (TensorProduct.rid R M).symm m = m ⊗ₜ 1 :=
  rfl
/-
**TensorProduct.toLinearMap_symm_rid** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：toLinearMap_symm_rid : (TensorProduct.rid R M).symm.toLinearMap = (mk R M 
R).flip 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_symm_rid : (TensorProduct.rid R M).symm.toLinearMap = (mk R M R).flip 1 := rfl

@[simp]
/-
**TensorProduct.comm_trans_lid** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：comm_trans_lid : TensorProduct.comm R M R ≪≫ₗ TensorProduct.lid R M = Tens
orProduct.rid R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
-/
theorem comm_trans_lid :
    TensorProduct.comm R M R ≪≫ₗ TensorProduct.lid R M = TensorProduct.rid R M :=
  LinearEquiv.toLinearMap_injective (ext (by ext; rfl))
/-
**TensorProduct.lid_comm** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_5} [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   (x : TensorProduct R M R), (TensorProduc
t.lid R M) ((TensorProduct.comm R M R) x) = (TensorProduct.rid R M) x
参数：x : TensorProduct R M R；TensorProduct.lid R M；(TensorProduct.comm R M R) x；Te
nsorProduct.rid R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.comm_trans_lid`：comm_trans_lid : TensorProduct.comm R M R 
≪≫ₗ TensorProduct.lid R M = TensorProduct.rid R M
-/
@[simp] lemma lid_comm (x) :
    TensorProduct.lid R M (TensorProduct.comm R M R x) = TensorProduct.rid R M x :=
  congr($comm_trans_lid _)

@[simp]
/-
**TensorProduct.comm_trans_rid** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：comm_trans_rid : TensorProduct.comm R R M ≪≫ₗ TensorProduct.rid R M = Tens
orProduct.lid R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem comm_trans_rid :
    TensorProduct.comm R R M ≪≫ₗ TensorProduct.rid R M = TensorProduct.lid R M :=
  LinearEquiv.toLinearMap_injective (ext (by ext; rfl))
/-
**TensorProduct.rid_comm** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_5} [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   (x : TensorProduct R R M), (TensorProduc
t.rid R M) ((TensorProduct.comm R R M) x) = (TensorProduct.lid R M) x
参数：x : TensorProduct R R M；TensorProduct.rid R M；(TensorProduct.comm R R M) x；Te
nsorProduct.lid R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.comm_trans_rid`：comm_trans_rid : TensorProduct.comm R R M 
≪≫ₗ TensorProduct.rid R M = TensorProduct.lid R M
-/
@[simp] lemma rid_comm (x) :
    TensorProduct.rid R M (TensorProduct.comm R R M x) = TensorProduct.lid R M x :=
  congr($comm_trans_rid _)

variable (R) in
/-
**TensorProduct.lid_eq_rid** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：lid_eq_rid : TensorProduct.lid R R = TensorProduct.rid R R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem lid_eq_rid : TensorProduct.lid R R = TensorProduct.rid R R :=
  LinearEquiv.toLinearMap_injective <| ext' mul_comm

section CompatibleSMul

variable (R A M N) [CommSemiring A] [Module A M] [Module A N]
  [CompatibleSMul R A M N] [Module R A] [SMulCommClass R A A] [CompatibleSMul R A A M]
  [CompatibleSMul A R A M]

/-- If the R- and A- action on A and M satisfy `CompatibleSMul` both ways,
then `A ⊗[R] M` is canonically isomorphic to `M`. -/
/-
**TensorProduct.lidOfCompatibleSMul** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：lidOfCompatibleSMul : A otimes[R] M ≃ₗ[A] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the R- and A- action on A and M satisfy `CompatibleSMul` both ways,
then `A ⊗[R] M` is canonically isomorphic to `M`.
-/
def lidOfCompatibleSMul : A ⊗[R] M ≃ₗ[A] M :=
  (equivOfCompatibleSMul R A A A M).symm ≪≫ₗ TensorProduct.lid _ _
/-
**TensorProduct.lidOfCompatibleSMul_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduc
t`。
形式化陈述：lidOfCompatibleSMul_tmul (a m) : lidOfCompatibleSMul R A M (a otimesₜ[R] m
) = a • m
参数：a m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lidOfCompatibleSMul_tmul (a m) : lidOfCompatibleSMul R A M (a ⊗ₜ[R] m) = a • m := rfl

variable {R} in
/-
**TensorProduct.CompatibleSMul.of_algebraMap_surjective** 是 Mathlib 中的一个定理，位于命名空
间 `TensorProduct.CompatibleSMul`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_5) (N : Type u_6) [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N] {A : Type u_11}   [inst_5 : CommSemiring A] [inst
_6 : Algebra R A] [inst_7 : _root_.Module A M] [IsScalarTower R A M]   [inst_9 :
 _root_.Module A N] [IsScalarTower R A N],   Function.Surjective ⇑(algebraMap R 
A) → TensorProduct.CompatibleSMul R A M N
参数：M : Type u_5；N : Type u_6；algebraMap R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `TensorProduct.CompatibleSMul.smul_tmul`：∀ {R : Type u_1} {R' : Type u_4}
 {inst : CommSemiring R} {inst_1 : Monoid R'} {M : Type u_7} {N : Type u_8}   {i
nst_2 : AddCommMonoid M} {in…
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma CompatibleSMul.of_algebraMap_surjective {A : Type*} [CommSemiring A] [Algebra R A]
    [Module A M] [IsScalarTower R A M] [Module A N] [IsScalarTower R A N]
    (h : Function.Surjective (algebraMap R A)) :
    CompatibleSMul R A M N where
  smul_tmul a m n := by
    obtain ⟨r, rfl⟩ := h a
    simp [smul_tmul]

end CompatibleSMul

open LinearMap

section

variable (R M N P)

attribute [local ext high] ext in
/-- The associator for tensor product of R-modules, as a linear equivalence. -/
/-
**TensorProduct.assoc** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：(R : Type u_1) →   [inst : CommSemiring R] →     (M : Type u_5) →       (N
 : Type u_6) →         (P : Type u_7) →           [inst_1 : AddCommMonoid M] →  
           [inst_2 : AddCommMonoid N] →               [inst_3 : AddCommMonoid P]
 →                 [inst_4 : _root_.Module R M] →                   [inst_5 : _r
oot_.Module R N] →                     [inst_6 : _root_.Module R P] →           
            TensorProduct R (TensorProduct R M N) P ≃ₗ[R] TensorProduct R M (Ten
sorProduct R N P)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator for tensor product of R-modules, as a linear equivalence.
-/
protected def assoc : M ⊗[R] N ⊗[R] P ≃ₗ[R] M ⊗[R] (N ⊗[R] P) :=
  LinearEquiv.ofLinearMap
    (lift <| lift <| lcurry _ _ _ _ ∘ₗ mk _ _ _)
    (lift <| uncurry _ _ _ _ ∘ₗ curry (mk R _ _))
    (by ext; rfl)
    (by ext; rfl)

end

@[simp]
/-
**TensorProduct.assoc_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：assoc_tmul (m : M) (n : N) (p : P) : (TensorProduct.assoc R M N P) (m otim
esₜ n otimesₜ p) = m otimesₜ (n otimesₜ p)
参数：m : M；n : N；p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem assoc_tmul (m : M) (n : N) (p : P) :
    (TensorProduct.assoc R M N P) (m ⊗ₜ n ⊗ₜ p) = m ⊗ₜ (n ⊗ₜ p) :=
  rfl

@[simp]
/-
**TensorProduct.assoc_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：assoc_symm_tmul (m : M) (n : N) (p : P) : (TensorProduct.assoc R M N P).sy
mm (m otimesₜ (n otimesₜ p)) = m otimesₜ n otimesₜ p
参数：m : M；n : N；p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem assoc_symm_tmul (m : M) (n : N) (p : P) :
    (TensorProduct.assoc R M N P).symm (m ⊗ₜ (n ⊗ₜ p)) = m ⊗ₜ n ⊗ₜ p :=
  rfl

/-- Given linear maps `f : M → Q`, `g : N → S`, and `h : P → T`, if we identify `(M ⊗ N) ⊗ P`
with `M ⊗ (N ⊗ P)` and `(Q ⊗ S) ⊗ T` with `Q ⊗ (S ⊗ T)`, then this lemma states that
`f ⊗ (g ⊗ h) = (f ⊗ g) ⊗ h`. -/
/-
**TensorProduct.map_map_comp_assoc_eq** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：map_map_comp_assoc_eq (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) :
 map f (map g h) ∘ₗ TensorProduct.assoc R M N P = TensorProduct.assoc R Q S T ∘ₗ
 map (map f g) h
参数：f : M ->ₗ[R] Q；g : N ->ₗ[R] S；h : P ->ₗ[R] T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g

--- 原说明 ---
Given linear maps `f : M → Q`, `g : N → S`, and `h : P → T`, if we identify `(M 
⊗ N) ⊗ P`
with `M ⊗ (N ⊗ P)` and `(Q ⊗ S) ⊗ T` with `Q ⊗ (S ⊗ T)`, then this lemma states 
that
`f ⊗ (g ⊗ h) = (f ⊗ g) ⊗ h`.
-/
lemma map_map_comp_assoc_eq (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) :
    map f (map g h) ∘ₗ TensorProduct.assoc R M N P =
      TensorProduct.assoc R Q S T ∘ₗ map (map f g) h :=
  ext <| ext <| LinearMap.ext fun _ => LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
/-
**TensorProduct.map_map_assoc** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：map_map_assoc (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) (x : M ot
imes[R] N otimes[R] P) : map f (map g h) (TensorProduct.assoc R M N P x) = Tenso
rProduct.assoc R Q S T (map (map f g) h x)
参数：f : M ->ₗ[R] Q；g : N ->ₗ[R] S；h : P ->ₗ[R] T；x : M otimes[R] N otimes[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `TensorProduct.map_map_comp_assoc_eq`：map_map_comp_assoc_eq (f : M ->ₗ[R]
 Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) : map f (map g h) ∘ₗ TensorProduct.assoc R
 M N P = TensorProduct.as…
-/
lemma map_map_assoc (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) (x : M ⊗[R] N ⊗[R] P) :
    map f (map g h) (TensorProduct.assoc R M N P x) =
      TensorProduct.assoc R Q S T (map (map f g) h x) :=
  DFunLike.congr_fun (map_map_comp_assoc_eq _ _ _) _

/-- Given linear maps `f : M → Q`, `g : N → S`, and `h : P → T`, if we identify `M ⊗ (N ⊗ P)`
with `(M ⊗ N) ⊗ P` and `Q ⊗ (S ⊗ T)` with `(Q ⊗ S) ⊗ T`, then this lemma states that
`(f ⊗ g) ⊗ h = f ⊗ (g ⊗ h)`. -/
/-
**TensorProduct.map_map_comp_assoc_symm_eq** 是 Mathlib 中的一个引理，位于命名空间 `TensorProd
uct`。
形式化陈述：map_map_comp_assoc_symm_eq (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R]
 T) : map (map f g) h ∘ₗ (TensorProduct.assoc R M N P).symm = (TensorProduct.ass
oc R Q S T).symm ∘ₗ map f (map g h)
参数：f : M ->ₗ[R] Q；g : N ->ₗ[R] S；h : P ->ₗ[R] T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g

--- 原说明 ---
Given linear maps `f : M → Q`, `g : N → S`, and `h : P → T`, if we identify `M ⊗
 (N ⊗ P)`
with `(M ⊗ N) ⊗ P` and `Q ⊗ (S ⊗ T)` with `(Q ⊗ S) ⊗ T`, then this lemma states 
that
`(f ⊗ g) ⊗ h = f ⊗ (g ⊗ h)`.
-/
lemma map_map_comp_assoc_symm_eq (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) :
    map (map f g) h ∘ₗ (TensorProduct.assoc R M N P).symm =
      (TensorProduct.assoc R Q S T).symm ∘ₗ map f (map g h) :=
  ext <| LinearMap.ext fun _ => ext <| LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
/-
**TensorProduct.map_map_assoc_symm** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：map_map_assoc_symm (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) (x :
 M otimes[R] (N otimes[R] P)) : map (map f g) h ((TensorProduct.assoc R M N P).s
ymm x) = (TensorProduct.assoc R Q S T).symm (map f (map g h) x)
参数：f : M ->ₗ[R] Q；g : N ->ₗ[R] S；h : P ->ₗ[R] T；x : M otimes[R] (N otimes[R] P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `TensorProduct.map_map_comp_assoc_symm_eq`：map_map_comp_assoc_symm_eq (f 
: M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) : map (map f g) h ∘ₗ (TensorProd
uct.assoc R M N P).symm = (Ten…
-/
lemma map_map_assoc_symm (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) (x : M ⊗[R] (N ⊗[R] P)) :
    map (map f g) h ((TensorProduct.assoc R M N P).symm x) =
      (TensorProduct.assoc R Q S T).symm (map f (map g h) x) :=
  DFunLike.congr_fun (map_map_comp_assoc_symm_eq _ _ _) _
/-
**TensorProduct.assoc_tensor** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：assoc_tensor : TensorProduct.assoc R (M otimes[R] N) Q S = .rTensor S (Ten
sorProduct.assoc R M N Q) ≪≫ₗ TensorProduct.assoc R M (N otimes[R] Q) S ≪≫ₗ .lTe
nsor M (TensorProduct.assoc R N Q S) ≪≫ₗ (TensorProduct.assoc R M N (Q otimes[R]
 S)).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.toLinearMap_inj`：toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e
₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂
· 使用定理 `TensorProduct.ext_fourfold`：ext_fourfold {g h : M otimes[R] N otimes[R] 
P otimes[R] Q ->ₛₗ[σ₁₂] P₂} (H : forall w x y z, g (w otimesₜ x otimesₜ y otimes
ₜ z) = h (w otim…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma assoc_tensor :
    TensorProduct.assoc R (M ⊗[R] N) Q S = .rTensor S (TensorProduct.assoc R M N Q) ≪≫ₗ
      TensorProduct.assoc R M (N ⊗[R] Q) S ≪≫ₗ .lTensor M (TensorProduct.assoc R N Q S) ≪≫ₗ
      (TensorProduct.assoc R M N (Q ⊗[R] S)).symm :=
  LinearEquiv.toLinearMap_inj.mp <| ext_fourfold fun _ _ _ => congrFun rfl
/-
**TensorProduct.assoc_tensor'** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：assoc_tensor' : TensorProduct.assoc R M (N otimes[R] Q) S = .rTensor S (Te
nsorProduct.assoc R M N Q).symm ≪≫ₗ (TensorProduct.assoc R (M otimes[R] N) Q S) 
≪≫ₗ TensorProduct.assoc R M N (Q otimes[R] S) ≪≫ₗ .lTensor M (TensorProduct.asso
c R N Q S).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.toLinearMap_inj`：toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e
₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂
· 使用定理 `TensorProduct.ext_fourfold''`：ext_fourfold'' {φ ψ : M otimes[R] (N otime
s[R] P) otimes[R] Q ->ₛₗ[σ₁₂] P₂} (H : forall w x y z, φ (w otimesₜ (x otimesₜ y
) otimesₜ z) = ψ (…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma assoc_tensor' :
    TensorProduct.assoc R M (N ⊗[R] Q) S = .rTensor S (TensorProduct.assoc R M N Q).symm ≪≫ₗ
      (TensorProduct.assoc R (M ⊗[R] N) Q S) ≪≫ₗ TensorProduct.assoc R M N (Q ⊗[R] S) ≪≫ₗ
      .lTensor M (TensorProduct.assoc R N Q S).symm :=
  LinearEquiv.toLinearMap_inj.mp <| ext_fourfold'' fun _ _ _ => congrFun rfl
/-
**TensorProduct.assoc_tensor''** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：assoc_tensor'' : TensorProduct.assoc R M N (Q otimes[R] S) = (TensorProduc
t.assoc R (M otimes[R] N) Q S).symm ≪≫ₗ .rTensor S (TensorProduct.assoc R M N Q)
 ≪≫ₗ TensorProduct.assoc R M (N otimes[R] Q) S ≪≫ₗ .lTensor M (TensorProduct.ass
oc R N Q S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.toLinearMap_inj`：toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e
₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂
· 使用定理 `TensorProduct.ext_fourfold'`：ext_fourfold' {φ ψ : M otimes[R] N otimes[R
] (P otimes[R] Q) ->ₛₗ[σ₁₂] P₂} (H : forall w x y z, φ (w otimesₜ x otimesₜ (y o
timesₜ z)) = ψ (w…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma assoc_tensor'' :
    TensorProduct.assoc R M N (Q ⊗[R] S) = (TensorProduct.assoc R (M ⊗[R] N) Q S).symm ≪≫ₗ
      .rTensor S (TensorProduct.assoc R M N Q) ≪≫ₗ TensorProduct.assoc R M (N ⊗[R] Q) S ≪≫ₗ
      .lTensor M (TensorProduct.assoc R N Q S) :=
  LinearEquiv.toLinearMap_inj.mp <| ext_fourfold' fun _ _ _ => congrFun rfl
/-
**TensorProduct.lid_tensor** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：lid_tensor : TensorProduct.lid R (M otimes[R] N) = (TensorProduct.assoc R 
R M N).symm ≪≫ₗ .rTensor N (TensorProduct.lid R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.toLinearMap_inj`：toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e
₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂
· 使用定理 `TensorProduct.ext_threefold'`：ext_threefold' {g h : M otimes[R] (N otime
s[R] P) ->ₛₗ[σ₁₂] P₂} (H : forall x y z, g (x otimesₜ (y otimesₜ z)) = h (x otim
esₜ (y otimesₜ z))…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma lid_tensor :
    TensorProduct.lid R (M ⊗[R] N) = (TensorProduct.assoc R R M N).symm ≪≫ₗ
      .rTensor N (TensorProduct.lid R M) :=
  LinearEquiv.toLinearMap_inj.mp <| ext_threefold' fun _ _ => congrFun rfl

section

variable {P' Q' : Type*}
variable [AddCommMonoid P'] [Module R P']
variable [AddCommMonoid Q'] [Module R Q']

variable (R M N P Q)

/-- A tensor product analogue of `mul_left_comm`. -/
/-
**TensorProduct.leftComm** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：leftComm : M otimes[R] (N otimes[R] P) ≃ₗ[R] N otimes[R] (M otimes[R] P)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A tensor product analogue of `mul_left_comm`.
-/
def leftComm : M ⊗[R] (N ⊗[R] P) ≃ₗ[R] N ⊗[R] (M ⊗[R] P) :=
  let e₁ := (TensorProduct.assoc R M N P).symm
  let e₂ := congr (TensorProduct.comm R M N) (1 : P ≃ₗ[R] P)
  let e₃ := TensorProduct.assoc R N M P
  e₁ ≪≫ₗ (e₂ ≪≫ₗ e₃)

variable {M N P Q}

@[simp]
/-
**TensorProduct.leftComm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：leftComm_tmul (m : M) (n : N) (p : P) : leftComm R M N P (m otimesₜ (n oti
mesₜ p)) = n otimesₜ (m otimesₜ p)
参数：m : M；n : N；p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftComm_tmul (m : M) (n : N) (p : P) : leftComm R M N P (m ⊗ₜ (n ⊗ₜ p)) = n ⊗ₜ (m ⊗ₜ p) :=
  rfl

@[simp]
/-
**TensorProduct.leftComm_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：leftComm_symm_tmul (m : M) (n : N) (p : P) : (leftComm R M N P).symm (n ot
imesₜ (m otimesₜ p)) = m otimesₜ (n otimesₜ p)
参数：m : M；n : N；p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftComm_symm_tmul (m : M) (n : N) (p : P) :
    (leftComm R M N P).symm (n ⊗ₜ (m ⊗ₜ p)) = m ⊗ₜ (n ⊗ₜ p) :=
  rfl

attribute [local ext high] TensorProduct.ext in
/-
**TensorProduct.leftComm_def** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：leftComm_def : leftComm R M N P = (TensorProduct.assoc R _ _ _).symm ≪≫ₗ c
ongr (TensorProduct.comm _ _ _) (.refl _ _) ≪≫ₗ (TensorProduct.assoc R _ _ _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
lemma leftComm_def : leftComm R M N P =
    (TensorProduct.assoc R _ _ _).symm ≪≫ₗ congr (TensorProduct.comm _ _ _) (.refl _ _) ≪≫ₗ
      (TensorProduct.assoc R _ _ _) := by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

variable (M N P) in
attribute [local ext high] ext in
/-- A tensor product analogue of `mul_right_comm`. -/
/-
**TensorProduct.rightComm** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：rightComm : M otimes[R] N otimes[R] P ≃ₗ[R] M otimes[R] P otimes[R] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A tensor product analogue of `mul_right_comm`.
-/
def rightComm : M ⊗[R] N ⊗[R] P ≃ₗ[R] M ⊗[R] P ⊗[R] N :=
  LinearEquiv.ofLinearMap
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ (mk _ _ _).compr₂ (mk _ _ _))))
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ (mk _ _ _).compr₂ (mk _ _ _))))
  (by ext; rfl) (by ext; rfl)

@[simp]
/-
**TensorProduct.rightComm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：rightComm_tmul (m : M) (n : N) (p : P) : rightComm R M N P ((m otimesₜ n) 
otimesₜ p) = (m otimesₜ p) otimesₜ n
参数：m : M；n : N；p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightComm_tmul (m : M) (n : N) (p : P) :
    rightComm R M N P ((m ⊗ₜ n) ⊗ₜ p) = (m ⊗ₜ p) ⊗ₜ n :=
  rfl

@[simp]
/-
**TensorProduct.rightComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：rightComm_symm : (rightComm R M N P).symm = rightComm R M P N
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightComm_symm : (rightComm R M N P).symm = rightComm R M P N := rfl

attribute [local ext high] TensorProduct.ext in
/-
**TensorProduct.rightComm_def** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：rightComm_def : rightComm R M N P = TensorProduct.assoc R _ _ _ ≪≫ₗ congr 
(.refl _ _) (TensorProduct.comm _ _ _) ≪≫ₗ (TensorProduct.assoc R _ _ _).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
lemma rightComm_def : rightComm R M N P =
    TensorProduct.assoc R _ _ _ ≪≫ₗ congr (.refl _ _) (TensorProduct.comm _ _ _) ≪≫ₗ
      (TensorProduct.assoc R _ _ _).symm := by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

variable (M N P Q)

/-- This special case is worth defining explicitly since it is useful for defining multiplication
on tensor products of modules carrying multiplications (e.g., associative rings, Lie rings, ...).

E.g., suppose `M = P` and `N = Q` and that `M` and `N` carry bilinear multiplications:
`M ⊗ M → M` and `N ⊗ N → N`. Using `map`, we can define `(M ⊗ M) ⊗ (N ⊗ N) → M ⊗ N` which, when
combined with this definition, yields a bilinear multiplication on `M ⊗ N`:
`(M ⊗ N) ⊗ (M ⊗ N) → M ⊗ N`. In particular we could use this to define the multiplication in
the `TensorProduct.semiring` instance (currently defined "by hand" using `TensorProduct.mul`).

See also `mul_mul_mul_comm`. -/
/-
**TensorProduct.tensorTensorTensorComm** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`
。
形式化陈述：tensorTensorTensorComm : M otimes[R] N otimes[R] (P otimes[R] Q) ≃ₗ[R] M o
times[R] P otimes[R] (N otimes[R] Q)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This special case is worth defining explicitly since it is useful for defining m
ultiplication
on tensor products of modules carrying multiplications (e.g., associative rings,
 Lie rings, ...).

E.g., suppose `M = P` and `N = Q` and that `M` and `N` carry bilinear multiplica
tions:
`M ⊗ M → M` and `N ⊗ N → N`. Using `map`, we can define `(M ⊗ M) ⊗ (N ⊗ N) → M ⊗
 N` which, when
combined with this definition, yields a bilinear multiplication on `M ⊗ N`:
`(M ⊗ N) ⊗ (M ⊗ N) → M ⊗ N`. In particular we could use this to define the multi
plication in
the `TensorProduct.semiring` instance (currently defined "by hand" using `Tensor
Product.mul`).

See also `mul_mul_mul_comm`.
-/
def tensorTensorTensorComm : M ⊗[R] N ⊗[R] (P ⊗[R] Q) ≃ₗ[R] M ⊗[R] P ⊗[R] (N ⊗[R] Q) :=
  (TensorProduct.assoc R (M ⊗[R] N) P Q).symm
    ≪≫ₗ congr (TensorProduct.rightComm R M N P) (.refl R Q)
    ≪≫ₗ TensorProduct.assoc R (M ⊗[R] P) N Q

variable {M N P Q}

@[simp]
/-
**TensorProduct.tensorTensorTensorComm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorPro
duct`。
形式化陈述：tensorTensorTensorComm_tmul (m : M) (n : N) (p : P) (q : Q) : tensorTensor
TensorComm R M N P Q (m otimesₜ n otimesₜ (p otimesₜ q)) = m otimesₜ p otimesₜ (
n otimesₜ q)
参数：m : M；n : N；p : P；q : Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorTensorTensorComm_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorComm R M N P Q (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ p ⊗ₜ (n ⊗ₜ q) :=
  rfl

@[simp]
/-
**TensorProduct.tensorTensorTensorComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `TensorPro
duct`。
形式化陈述：tensorTensorTensorComm_symm : (tensorTensorTensorComm R M N P Q).symm = te
nsorTensorTensorComm R M P N Q
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorTensorTensorComm_symm :
    (tensorTensorTensorComm R M N P Q).symm = tensorTensorTensorComm R M P N Q :=
  rfl
/-
**TensorProduct.tensorTensorTensorComm_trans_tensorTensorTensorComm** 是 Mathlib 
中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ (R : Type u_1) [inst : CommSemiring R] {M : Type u_5} {N : Type u_6} {P 
: Type u_7} {Q : Type u_8}   [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid 
N] [inst_3 : AddCommMonoid P] [inst_4 : AddCommMonoid Q]   [inst_5 : _root_.Modu
le R M] [inst_6 : _root_.Module R N] [inst_7 : _root_.Module R Q] [inst_8 : _roo
t_.Module R P],   TensorProduct.tensorTensorTensorComm R M N P Q ≪≫ₗ TensorProdu
ct.tensorTensorTensorComm R M P N Q =     LinearEquiv.refl R (TensorProduct R (T
ensorProduct R M N) (TensorProduct R P Q))
参数：R : Type u_1；TensorProduct R (TensorProduct R M N) (TensorProduct R P Q)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.tensorTensorTensorComm_symm`：tensorTensorTensorComm_symm :
 (tensorTensorTensorComm R M N P Q).symm = tensorTensorTensorComm R M P N Q
· 使用定理 `LinearEquiv.symm_trans_self`：symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.sy
mm.trans f = LinearEquiv.refl R₂ M₂
-/
@[simp] theorem tensorTensorTensorComm_trans_tensorTensorTensorComm :
    tensorTensorTensorComm R M N P Q ≪≫ₗ tensorTensorTensorComm R M P N Q = .refl R _ := by
  rw [← tensorTensorTensorComm_symm]
  exact LinearEquiv.symm_trans_self _
/-
**TensorProduct.tensorTensorTensorComm_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `Tenso
rProduct`。
形式化陈述：tensorTensorTensorComm_comp_map {V W : Type*} [AddCommMonoid V] [AddCommMo
noid W] [Module R V] [Module R W] (f : M ->ₗ[R] S) (g : N ->ₗ[R] T) (h : P ->ₗ[R
] V) (j : Q ->ₗ[R] W) : tensorTensorTensorComm R S T V W ∘ₗ map (map f g) (map h
 j) = map (map f h) (map g j) ∘ₗ tensorTensorTensorComm R M N P Q
参数：f : M ->ₗ[R] S；g : N ->ₗ[R] T；h : P ->ₗ[R] V；j : Q ->ₗ[R] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext_fourfold'`：ext_fourfold' {φ ψ : M otimes[R] N otimes[R
] (P otimes[R] Q) ->ₛₗ[σ₁₂] P₂} (H : forall w x y z, φ (w otimesₜ x otimesₜ (y o
timesₜ z)) = ψ (w…
-/
theorem tensorTensorTensorComm_comp_map {V W : Type*}
    [AddCommMonoid V] [AddCommMonoid W] [Module R V] [Module R W]
    (f : M →ₗ[R] S) (g : N →ₗ[R] T) (h : P →ₗ[R] V) (j : Q →ₗ[R] W) :
    tensorTensorTensorComm R S T V W ∘ₗ map (map f g) (map h j) =
      map (map f h) (map g j) ∘ₗ tensorTensorTensorComm R M N P Q :=
  ext_fourfold' fun _ _ _ _ => rfl

variable (M N P Q)

/-- This special case is useful for describing the interplay between `dualTensorHomEquiv` and
composition of linear maps.

E.g., composition of linear maps gives a map `(M → N) ⊗ (N → P) → (M → P)`, and applying
`dual_tensor_hom_equiv.symm` to the three hom-modules gives a map
`(M.dual ⊗ N) ⊗ (N.dual ⊗ P) → (M.dual ⊗ P)`, which agrees with the application of `contractRight`
on `N ⊗ N.dual` after the suitable rebracketing.
-/
/-
**TensorProduct.tensorTensorTensorAssoc** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct
`。
形式化陈述：tensorTensorTensorAssoc : M otimes[R] N otimes[R] (P otimes[R] Q) ≃ₗ[R] M 
otimes[R] (N otimes[R] P) otimes[R] Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This special case is useful for describing the interplay between `dualTensorHomE
quiv` and
composition of linear maps.

E.g., composition of linear maps gives a map `(M → N) ⊗ (N → P) → (M → P)`, and 
applying
`dual_tensor_hom_equiv.symm` to the three hom-modules gives a map
`(M.dual ⊗ N) ⊗ (N.dual ⊗ P) → (M.dual ⊗ P)`, which agrees with the application 
of `contractRight`
on `N ⊗ N.dual` after the suitable rebracketing.
-/
def tensorTensorTensorAssoc : M ⊗[R] N ⊗[R] (P ⊗[R] Q) ≃ₗ[R] M ⊗[R] (N ⊗[R] P) ⊗[R] Q :=
  (TensorProduct.assoc R (M ⊗[R] N) P Q).symm ≪≫ₗ
    congr (TensorProduct.assoc R M N P) (1 : Q ≃ₗ[R] Q)

variable {M N P Q}

@[simp]
/-
**TensorProduct.tensorTensorTensorAssoc_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorPr
oduct`。
形式化陈述：tensorTensorTensorAssoc_tmul (m : M) (n : N) (p : P) (q : Q) : tensorTenso
rTensorAssoc R M N P Q (m otimesₜ n otimesₜ (p otimesₜ q)) = m otimesₜ (n otimes
ₜ p) otimesₜ q
参数：m : M；n : N；p : P；q : Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorTensorTensorAssoc_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorAssoc R M N P Q (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ (n ⊗ₜ p) ⊗ₜ q :=
  rfl

@[simp]
/-
**TensorProduct.tensorTensorTensorAssoc_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Ten
sorProduct`。
形式化陈述：tensorTensorTensorAssoc_symm_tmul (m : M) (n : N) (p : P) (q : Q) : (tenso
rTensorTensorAssoc R M N P Q).symm (m otimesₜ (n otimesₜ p) otimesₜ q) = m otime
sₜ n otimesₜ (p otimesₜ q)
参数：m : M；n : N；p : P；q : Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorTensorTensorAssoc_symm_tmul (m : M) (n : N) (p : P) (q : Q) :
    (tensorTensorTensorAssoc R M N P Q).symm (m ⊗ₜ (n ⊗ₜ p) ⊗ₜ q) = m ⊗ₜ n ⊗ₜ (p ⊗ₜ q) :=
  rfl

end

end TensorProduct

open scoped TensorProduct

variable [Module R P]

namespace LinearMap

variable {N}

variable (g : P →ₗ[R] Q) (f : N →ₗ[R] P)

open TensorProduct (assoc lid rid)

/-
**LinearMap.lTensor_tensor** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_tensor (f : P ->ₗ[R] Q) : lTensor (M otimes[R] N) f = (assoc R M N
 Q).symm ∘ₗ (f.lTensor N).lTensor M ∘ₗ assoc R M N P
参数：f : P ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
-/
lemma lTensor_tensor (f : P →ₗ[R] Q) :
    lTensor (M ⊗[R] N) f = (assoc R M N Q).symm ∘ₗ (f.lTensor N).lTensor M ∘ₗ assoc R M N P :=
  TensorProduct.ext <| TensorProduct.ext rfl
/-
**LinearMap.rTensor_tensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_tensor : rTensor (M otimes[R] N) g = assoc R Q M N ∘ₗ rTensor N (r
Tensor M g) ∘ₗ (assoc R P M N).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem rTensor_tensor : rTensor (M ⊗[R] N) g =
    assoc R Q M N ∘ₗ rTensor N (rTensor M g) ∘ₗ (assoc R P M N).symm :=
  TensorProduct.ext <| LinearMap.ext fun _ ↦ TensorProduct.ext rfl

open TensorProduct
/-
**LinearMap.lid_comp_rTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lid_comp_rTensor (f : N ->ₗ[R] R) : (lid R M).comp (rTensor M f) = lift ((
lsmul R M).comp f)
参数：f : N ->ₗ[R] R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
-/
theorem lid_comp_rTensor (f : N →ₗ[R] R) :
    (lid R M).comp (rTensor M f) = lift ((lsmul R M).comp f) := ext' fun _ _ ↦ rfl
/-
**LinearMap.rid_comp_lTensor** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：rid_comp_lTensor (f : M ->ₗ[R] R) : (rid R N).comp (lTensor N f) = lift ((
lsmul R N).flip.compl₂ f)
参数：f : M ->ₗ[R] R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
lemma rid_comp_lTensor (f : M →ₗ[R] R) :
    (rid R N).comp (lTensor N f) = lift ((lsmul R N).flip.compl₂ f) := ext' fun _ _ ↦ rfl
/-
**LinearMap.lTensor_rTensor_comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_rTensor_comp_assoc (x : M ->ₗ[R] N) : lTensor P (rTensor Q x) ∘ₗ T
ensorProduct.assoc R P M Q = TensorProduct.assoc R P N Q ∘ₗ rTensor Q (lTensor P
 x)
参数：x : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.map_map_comp_assoc_eq`：map_map_comp_assoc_eq (f : M ->ₗ[R]
 Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) : map f (map g h) ∘ₗ TensorProduct.assoc R
 M N P = TensorProduct.as…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lTensor_rTensor_comp_assoc (x : M →ₗ[R] N) :
    lTensor P (rTensor Q x) ∘ₗ TensorProduct.assoc R P M Q
    = TensorProduct.assoc R P N Q ∘ₗ rTensor Q (lTensor P x) := by
  simp_rw [rTensor, lTensor, map_map_comp_assoc_eq]
/-
**LinearMap.rTensor_lTensor_comp_assoc_symm** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
`。
形式化陈述：rTensor_lTensor_comp_assoc_symm (x : M ->ₗ[R] N) : rTensor Q (lTensor P x)
 ∘ₗ (TensorProduct.assoc R P M Q).symm = (TensorProduct.assoc R P N Q).symm ∘ₗ l
Tensor P (rTensor Q x)
参数：x : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.map_map_comp_assoc_symm_eq`：map_map_comp_assoc_symm_eq (f 
: M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) : map (map f g) h ∘ₗ (TensorProd
uct.assoc R M N P).symm = (Ten…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rTensor_lTensor_comp_assoc_symm (x : M →ₗ[R] N) :
    rTensor Q (lTensor P x) ∘ₗ (TensorProduct.assoc R P M Q).symm
    = (TensorProduct.assoc R P N Q).symm ∘ₗ lTensor P (rTensor Q x) := by
  simp_rw [rTensor, lTensor, map_map_comp_assoc_symm_eq]

end LinearMap

namespace Equiv
variable {R A A' B B' C C' : Type*}
variable [CommSemiring R] [AddCommMonoid A'] [AddCommMonoid B'] [AddCommMonoid C']
variable [Module R A'] [Module R B'] [Module R C']

variable (R) in
open TensorProduct in
/-
**Equiv.tensorProductAssoc_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：tensorProductAssoc_def (eA : A ≃ A') (eB : B ≃ B') (eC : C ≃ C') : letI
参数：eA : A ≃ A'；eB : B ≃ B'；eC : C ≃ C'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
lemma tensorProductAssoc_def (eA : A ≃ A') (eB : B ≃ B') (eC : C ≃ C') :
    letI := eA.addCommMonoid
    letI := eB.addCommMonoid
    letI := eC.addCommMonoid
    letI := eA.module R
    letI := eB.module R
    letI := eC.module R
    TensorProduct.assoc R A B C = .trans
      (congr (congr (eA.linearEquiv R) (eB.linearEquiv R)) (eC.linearEquiv R)) (.trans
      (TensorProduct.assoc R A' B' C') <| congr (eA.linearEquiv R).symm <|
        congr (eB.linearEquiv R).symm (eC.linearEquiv R).symm) := by
  ext x
  induction x with
  | zero => simp
  | add => simp [*]
  | tmul x a => induction x <;> simp [*, add_tmul]

end Equiv

