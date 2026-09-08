/-
Copyright (c) 2023 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Coalgebras

In this file we define `Coalgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toCoalgebra`
* Binary products: `Prod.instCoalgebra`
* Finitely supported functions: `DFinsupp.instCoalgebra`, `Finsupp.instCoalgebra`
* Finite pi functions: `Pi.instCoalgebra`

## References

* <https://en.wikipedia.org/wiki/Coalgebra>
-/

@[expose] public section

universe u v w

open scoped TensorProduct

/-- Data fields for `Coalgebra`, to allow API to be constructed before proving `Coalgebra.coassoc`.

See `Coalgebra` for documentation. -/
/-
**CoalgebraStruct** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   (A : Type v) → [inst : CommSemiring R] → [inst_1 : AddCom
mMonoid A] → [_root_.Module R A] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Data fields for `Coalgebra`, to allow API to be constructed before proving `Coal
gebra.coassoc`.

See `Coalgebra` for documentation.
-/
class CoalgebraStruct (R : Type u) (A : Type v)
    [CommSemiring R] [AddCommMonoid A] [Module R A] where
  /-- The comultiplication of the coalgebra -/
  comul : A →ₗ[R] A ⊗[R] A
  /-- The counit of the coalgebra -/
  counit : A →ₗ[R] R

@[inherit_doc] scoped[RingTheory.LinearMap] notation "ε" => CoalgebraStruct.counit
@[inherit_doc] scoped[RingTheory.LinearMap] notation "δ" => CoalgebraStruct.comul

/--
A representation of an element `a` of a coalgebra `A` is a finite sum of pure tensors `∑ xᵢ ⊗ yᵢ`
that is equal to `comul a`.
-/
/-
**Coalgebra.Repr** 是 Mathlib 中的一个归纳类型，位于命名空间 `Coalgebra`。
形式化陈述：(R : Type u) →   {A : Type v} →     [inst : CommSemiring R] →       [inst_
1 : AddCommMonoid A] →         [inst_2 : _root_.Module R A] → [CoalgebraStruct R
 A] → A → Type u_1 → Type (max u_1 v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A representation of an element `a` of a coalgebra `A` is a finite sum of pure te
nsors `∑ xᵢ ⊗ yᵢ`
that is equal to `comul a`.
-/
structure Coalgebra.Repr (R : Type u) {A : Type v}
    [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A] (a : A) (ι : Type*) where
  /-- the finite indexing set of a representation of `comul a` -/
  (index : Finset ι)
  /-- the first coordinate of a representation of `comul a` -/
  (left : ι → A)
  /-- the second coordinate of a representation of `comul a` -/
  (right : ι → A)
  /-- `comul a` is equal to a finite sum of some pure tensors -/
  (eq : ∑ i ∈ index, left i ⊗ₜ[R] right i = CoalgebraStruct.comul a)

/-- An arbitrarily chosen representation. -/
/-
**Coalgebra.Repr.arbitrary** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Coalgebra.Repr.arbitrary (R : Type u) {A : Type v} [CommSemiring R] [AddCo
mmMonoid A] [Module R A] [CoalgebraStruct R A] (a : A) : Coalgebra.Repr R a (A ×
 A) where left
参数：R : Type u；a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrarily chosen representation.
-/
noncomputable def Coalgebra.Repr.arbitrary (R : Type u) {A : Type v}
    [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A] (a : A) :
    Coalgebra.Repr R a (A × A) where
  left := Prod.fst
  right := Prod.snd
  index := TensorProduct.exists_finset (R := R) (CoalgebraStruct.comul a) |>.choose
  eq := TensorProduct.exists_finset (R := R) (CoalgebraStruct.comul a) |>.choose_spec.symm

@[inherit_doc Coalgebra.Repr.arbitrary]
scoped[Coalgebra] notation "ℛ" => Coalgebra.Repr.arbitrary

namespace Coalgebra
export CoalgebraStruct (comul counit)
end Coalgebra

/-- A coalgebra over a commutative (semi)ring `R` is an `R`-module equipped with a coassociative
comultiplication `Δ` and a counit `ε` obeying the left and right counitality laws. -/
/-
**Coalgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   (A : Type v) → [inst : CommSemiring R] → [inst_1 : AddCom
mMonoid A] → [_root_.Module R A] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coalgebra over a commutative (semi)ring `R` is an `R`-module equipped with a c
oassociative
comultiplication `Δ` and a counit `ε` obeying the left and right counitality law
s.
-/
class Coalgebra (R : Type u) (A : Type v)
    [CommSemiring R] [AddCommMonoid A] [Module R A] extends CoalgebraStruct R A where
  /-- The comultiplication is coassociative -/
  coassoc : TensorProduct.assoc R A A A ∘ₗ comul.rTensor A ∘ₗ comul = comul.lTensor A ∘ₗ comul
  /-- The counit satisfies the left counitality law -/
  rTensor_counit_comp_comul : counit.rTensor A ∘ₗ comul = TensorProduct.mk R _ _ 1
  /-- The counit satisfies the right counitality law -/
  lTensor_counit_comp_comul : counit.lTensor A ∘ₗ comul = (TensorProduct.mk R _ _).flip 1

namespace Coalgebra
variable {R : Type u} {A : Type v} {ι : Type*} {κ Λ : ι → Type*}
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A] {a : A}

/-- The indexing type of a representation of `comul a` -/
@[nolint unusedArguments, deprecated "The indexing type is now unbundled" (since := "2026-05-31")]
/-
**Coalgebra.Repr.** 是 Mathlib 中的一个缩写定义，位于命名空间 `Coalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The indexing type of a representation of `comul a`
-/
protected abbrev Repr.ι (_repr : Repr R a ι) : Type _ := ι

@[simp]
/-
**Coalgebra.coassoc_apply** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra`。
形式化陈述：coassoc_apply (a : A) : TensorProduct.assoc R A A A (comul.rTensor A (comu
l a)) = comul.lTensor A (comul a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Coalgebra.coassoc`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R} {
inst_1 : AddCommMonoid A} {inst_2 : _root_.Module R A}   [self : Coalgebra R A],
   ↑(Te…
-/
theorem coassoc_apply (a : A) :
    TensorProduct.assoc R A A A (comul.rTensor A (comul a)) = comul.lTensor A (comul a) :=
  LinearMap.congr_fun coassoc a

@[simp]
/-
**Coalgebra.coassoc_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra`。
形式化陈述：coassoc_symm_apply (a : A) : (TensorProduct.assoc R A A A).symm (comul.lTe
nsor A (comul a)) = comul.rTensor A (comul a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `Coalgebra.coassoc_apply`：coassoc_apply (a : A) : TensorProduct.assoc R A
 A A (comul.rTensor A (comul a)) = comul.lTensor A (comul a)
-/
theorem coassoc_symm_apply (a : A) :
    (TensorProduct.assoc R A A A).symm (comul.lTensor A (comul a)) = comul.rTensor A (comul a) := by
  rw [(TensorProduct.assoc R A A A).symm_apply_eq, coassoc_apply a]

@[simp]
/-
**Coalgebra.coassoc_symm** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra`。
形式化陈述：coassoc_symm : (TensorProduct.assoc R A A A).symm ∘ₗ comul.lTensor A ∘ₗ co
mul = comul.rTensor A ∘ₗ (comul (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Coalgebra.coassoc_symm_apply`：coassoc_symm_apply (a : A) : (TensorProduc
t.assoc R A A A).symm (comul.lTensor A (comul a)) = comul.rTensor A (comul a)
-/
theorem coassoc_symm :
    (TensorProduct.assoc R A A A).symm ∘ₗ comul.lTensor A ∘ₗ comul =
    comul.rTensor A ∘ₗ (comul (R := R)) :=
  LinearMap.ext coassoc_symm_apply

@[simp]
/-
**Coalgebra.rTensor_counit_comul** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra`。
形式化陈述：rTensor_counit_comul (a : A) : counit.rTensor A (comul a) = 1 otimesₜ[R] a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Coalgebra.rTensor_counit_comp_comul`：∀ {R : Type u} {A : Type v} {inst :
 CommSemiring R} {inst_1 : AddCommMonoid A} {inst_2 : _root_.Module R A}   [self
 : Coalgebra R A],   Line…
-/
theorem rTensor_counit_comul (a : A) : counit.rTensor A (comul a) = 1 ⊗ₜ[R] a :=
  LinearMap.congr_fun rTensor_counit_comp_comul a

@[simp]
/-
**Coalgebra.lTensor_counit_comul** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra`。
形式化陈述：lTensor_counit_comul (a : A) : counit.lTensor A (comul a) = a otimesₜ[R] 1
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Coalgebra.lTensor_counit_comp_comul`：∀ {R : Type u} {A : Type v} {inst :
 CommSemiring R} {inst_1 : AddCommMonoid A} {inst_2 : _root_.Module R A}   [self
 : Coalgebra R A],   Line…
-/
theorem lTensor_counit_comul (a : A) : counit.lTensor A (comul a) = a ⊗ₜ[R] 1 :=
  LinearMap.congr_fun lTensor_counit_comp_comul a

@[simp]
/-
**Coalgebra.sum_counit_tmul_eq** 是 Mathlib 中的一个引理，位于命名空间 `Coalgebra`。
形式化陈述：sum_counit_tmul_eq (repr : Repr R a ι) : ∑ i in repr.index, counit (R
参数：repr : Repr R a ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Coalgebra.Repr.eq`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [
inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3 : CoalgebraStru
ct R A]…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Coalgebra.rTensor_counit_comp_comul`：∀ {R : Type u} {A : Type v} {inst :
 CommSemiring R} {inst_1 : AddCommMonoid A} {inst_2 : _root_.Module R A}   [self
 : Coalgebra R A],   Line…
-/
lemma sum_counit_tmul_eq (repr : Repr R a ι) :
    ∑ i ∈ repr.index, counit (R := R) (repr.left i) ⊗ₜ (repr.right i) = 1 ⊗ₜ[R] a := by
  simpa [← repr.eq, map_sum] using congr($(rTensor_counit_comp_comul (R := R) (A := A)) a)

@[simp]
/-
**Coalgebra.sum_tmul_counit_eq** 是 Mathlib 中的一个引理，位于命名空间 `Coalgebra`。
形式化陈述：sum_tmul_counit_eq (repr : Repr R a ι) : ∑ i in repr.index, (repr.left i) 
otimesₜ counit (R
参数：repr : Repr R a ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Coalgebra.Repr.eq`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [
inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3 : CoalgebraStru
ct R A]…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Coalgebra.lTensor_counit_comp_comul`：∀ {R : Type u} {A : Type v} {inst :
 CommSemiring R} {inst_1 : AddCommMonoid A} {inst_2 : _root_.Module R A}   [self
 : Coalgebra R A],   Line…
-/
lemma sum_tmul_counit_eq (repr : Repr R a ι) :
    ∑ i ∈ repr.index, (repr.left i) ⊗ₜ counit (R := R) (repr.right i) = a ⊗ₜ[R] 1 := by
  simpa [← repr.eq, map_sum] using congr($(lTensor_counit_comp_comul (R := R) (A := A)) a)

-- Cannot be @[simp] because `a₂` cannot be inferred by `simp`.
/-
**Coalgebra.sum_tmul_tmul_eq** 是 Mathlib 中的一个引理，位于命名空间 `Coalgebra`。
形式化陈述：sum_tmul_tmul_eq (repr : Repr R a ι) (a₁ : (i : ι) -> Repr R (repr.left i)
 (κ i)) (a₂ : (i : ι) -> Repr R (repr.right i) (Λ i)) : ∑ i in repr.index, ∑ j i
n (a₁ i).index, (a₁ i).left j otimesₜ[R] ((a₁ i).right j otimesₜ[R] repr.right i
) = ∑ i in repr.index, ∑ j in (a₂ i).index, repr.left i otimesₜ[R] ((a₂ i).left 
j otimesₜ[R] (a₂ i).right j)
参数：repr : Repr R a ι；a₁ : (i : ι) -> Repr R (repr.left i) (κ i)；a₂ : (i : ι) -> 
Repr R (repr.right i) (Λ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Coalgebra.Repr.eq`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [
inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3 : CoalgebraStru
ct R A]…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.sum_tmul`：sum_tmul {α : Type*} (s : Finset α) (m : α -> M)
 (n : N) : (∑ a in s, m a) otimesₜ[R] n = ∑ a in s, m a otimesₜ[R] n
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Coalgebra.coassoc`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R} {
inst_1 : AddCommMonoid A} {inst_2 : _root_.Module R A}   [self : Coalgebra R A],
   ↑(Te…
-/
lemma sum_tmul_tmul_eq (repr : Repr R a ι)
    (a₁ : (i : ι) → Repr R (repr.left i) (κ i)) (a₂ : (i : ι) → Repr R (repr.right i) (Λ i)) :
    ∑ i ∈ repr.index, ∑ j ∈ (a₁ i).index,
      (a₁ i).left j ⊗ₜ[R] ((a₁ i).right j ⊗ₜ[R] repr.right i)
      = ∑ i ∈ repr.index, ∑ j ∈ (a₂ i).index,
      repr.left i ⊗ₜ[R] ((a₂ i).left j ⊗ₜ[R] (a₂ i).right j) := by
  simpa [(a₂ _).eq, ← (a₁ _).eq, ← TensorProduct.tmul_sum,
    TensorProduct.sum_tmul, ← repr.eq] using congr($(coassoc (R := R)) a)

@[simp]
/-
**Coalgebra.sum_counit_tmul_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra`。
形式化陈述：sum_counit_tmul_map_eq {B : Type*} [AddCommMonoid B] [Module R B] {F : Typ
e*} [FunLike F A B] [LinearMapClass F R A B] (f : F) (a : A) {repr : Repr R a ι}
 : ∑ i in repr.index, counit (R
参数：f : F；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Coalgebra.sum_counit_tmul_eq`：sum_counit_tmul_eq (repr : Repr R a ι) : ∑
 i in repr.index, counit (R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_counit_tmul_map_eq {B : Type*} [AddCommMonoid B] [Module R B]
    {F : Type*} [FunLike F A B] [LinearMapClass F R A B] (f : F) (a : A) {repr : Repr R a ι} :
    ∑ i ∈ repr.index, counit (R := R) (repr.left i) ⊗ₜ f (repr.right i) = 1 ⊗ₜ[R] f a := by
  have := sum_counit_tmul_eq repr
  apply_fun LinearMap.lTensor R (f : A →ₗ[R] B) at this
  simp_all only [map_sum, LinearMap.lTensor_tmul, LinearMap.coe_coe]

@[simp]
/-
**Coalgebra.sum_map_tmul_counit_eq** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra`。
形式化陈述：sum_map_tmul_counit_eq {B : Type*} [AddCommMonoid B] [Module R B] {F : Typ
e*} [FunLike F A B] [LinearMapClass F R A B] (f : F) (a : A) {repr : Repr R a ι}
 : ∑ i in repr.index, f (repr.left i) otimesₜ counit (R
参数：f : F；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Coalgebra.sum_tmul_counit_eq`：sum_tmul_counit_eq (repr : Repr R a ι) : ∑
 i in repr.index, (repr.left i) otimesₜ counit (R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_map_tmul_counit_eq {B : Type*} [AddCommMonoid B] [Module R B]
    {F : Type*} [FunLike F A B] [LinearMapClass F R A B] (f : F) (a : A) {repr : Repr R a ι} :
    ∑ i ∈ repr.index, f (repr.left i) ⊗ₜ counit (R := R) (repr.right i) = f a ⊗ₜ[R] 1 := by
  have := sum_tmul_counit_eq repr
  apply_fun LinearMap.rTensor R (f : A →ₗ[R] B) at this
  simp_all only [map_sum, LinearMap.rTensor_tmul, LinearMap.coe_coe]

-- Cannot be @[simp] because `a₁` cannot be inferred by `simp`.
/-
**Coalgebra.sum_map_tmul_tmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra`。
形式化陈述：sum_map_tmul_tmul_eq {B : Type*} [AddCommMonoid B] [Module R B] {F : Type*
} [FunLike F A B] [LinearMapClass F R A B] (f g h : F) (a : A) {repr : Repr R a 
ι} {a₁ : (i : ι) -> Repr R (repr.left i) (κ i)} {a₂ : (i : ι) -> Repr R (repr.ri
ght i) (Λ i)} : ∑ i in repr.index, ∑ j in (a₂ i).index, f (repr.left i) otimesₜ 
(g ((a₂ i).left j) otimesₜ h ((a₂ i).right j)) = ∑ i in repr.index, ∑ j in (a₁ i
).index, f ((a₁ i).left j) otimesₜ[R] (g ((a₁ i).right j) otimesₜ[R] h (repr.rig
ht i))
参数：f g h : F；a : A；i : ι；repr.left i；κ i；i : ι；repr.right i；Λ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Coalgebra.sum_tmul_tmul_eq`：sum_tmul_tmul_eq (repr : Repr R a ι) (a₁ : (
i : ι) -> Repr R (repr.left i) (κ i)) (a₂ : (i : ι) -> Repr R (repr.right i) (Λ 
i)) : ∑ i in rep…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_map_tmul_tmul_eq {B : Type*} [AddCommMonoid B] [Module R B]
    {F : Type*} [FunLike F A B] [LinearMapClass F R A B] (f g h : F) (a : A) {repr : Repr R a ι}
    {a₁ : (i : ι) → Repr R (repr.left i) (κ i)} {a₂ : (i : ι) → Repr R (repr.right i) (Λ i)} :
    ∑ i ∈ repr.index, ∑ j ∈ (a₂ i).index,
      f (repr.left i) ⊗ₜ (g ((a₂ i).left j) ⊗ₜ h ((a₂ i).right j)) =
    ∑ i ∈ repr.index, ∑ j ∈ (a₁ i).index,
      f ((a₁ i).left j) ⊗ₜ[R] (g ((a₁ i).right j) ⊗ₜ[R] h (repr.right i)) := by
  have := sum_tmul_tmul_eq repr a₁ a₂
  apply_fun TensorProduct.map (f : A →ₗ[R] B)
    (TensorProduct.map (g : A →ₗ[R] B) (h : A →ₗ[R] B)) at this
  simp_all only [map_sum, TensorProduct.map_tmul, LinearMap.coe_coe]
/-
**Coalgebra.sum_counit_smul** 是 Mathlib 中的一个引理，位于命名空间 `Coalgebra`。
形式化陈述：sum_counit_smul (𝓡 : Repr R a ι) : ∑ x in 𝓡.index, counit (R
参数：𝓡 : Repr R a ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `Coalgebra.sum_counit_tmul_eq`：sum_counit_tmul_eq (repr : Repr R a ι) : ∑
 i in repr.index, counit (R
-/
lemma sum_counit_smul (𝓡 : Repr R a ι) :
    ∑ x ∈ 𝓡.index, counit (R := R) (𝓡.left x) • 𝓡.right x = a := by
  simpa only [map_sum, TensorProduct.lift.tmul, LinearMap.lsmul_apply, one_smul]
    using congr(TensorProduct.lift (LinearMap.lsmul R A) $(sum_counit_tmul_eq (R := R) 𝓡))
/-
**Coalgebra.lift_lsmul_comp_counit_comp_comul** 是 Mathlib 中的一个引理，位于命名空间 `Coalgeb
ra`。
形式化陈述：lift_lsmul_comp_counit_comp_comul : TensorProduct.lift (.lsmul R A ∘ₗ coun
it) ∘ₗ comul = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Coalgebra.rTensor_counit_comp_comul`：∀ {R : Type u} {A : Type v} {inst :
 CommSemiring R} {inst_1 : AddCommMonoid A} {inst_2 : _root_.Module R A}   [self
 : Coalgebra R A],   Line…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.compl₂_id`：compl₂_id (h : M ->ₛₗ[σ₁₅] N ->ₛₗ[σ₂₃] P) : h.compl
₂ LinearMap.id = h
· 使用定理 `TensorProduct.lift_comp_map`：lift_comp_map (i : M₂ ->ₛₗ[σ₂₃] N₂ ->ₛₗ[σ₂₃
] P₃) (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) : (lift i).comp (map f g) = lift
 ((i.comp f).comp…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearMap.rTensor.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (M : Ty
pe u_7) {N : Type u_8} {P : Type u_9} [inst_1 : AddCommMonoid M]   [inst_2 : Add
CommMonoid N…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_lsmul_comp_counit_comp_comul :
    TensorProduct.lift (.lsmul R A ∘ₗ counit) ∘ₗ comul = .id := by
  have := rTensor_counit_comp_comul (R := R) (A := A)
  apply_fun (TensorProduct.lift (LinearMap.lsmul R A) ∘ₗ ·) at this
  rw [LinearMap.rTensor, ← LinearMap.comp_assoc, TensorProduct.lift_comp_map, LinearMap.compl₂_id]
    at this
  ext
  simp [this]

variable (R A) in
/-- A coalgebra `A` is cocommutative if its comultiplication `δ : A → A ⊗ A` commutes with the
swapping `β : A ⊗ A ≃ A ⊗ A` of the factors in the tensor product. -/
/-
**Coalgebra.IsCocomm** 是 Mathlib 中的一个归纳类型，位于命名空间 `Coalgebra`。
形式化陈述：(R : Type u) →   (A : Type v) →     [inst : CommSemiring R] → [inst_1 : Ad
dCommMonoid A] → [inst_2 : _root_.Module R A] → [Coalgebra R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coalgebra `A` is cocommutative if its comultiplication `δ : A → A ⊗ A` commute
s with the
swapping `β : A ⊗ A ≃ A ⊗ A` of the factors in the tensor product.
-/
class IsCocomm where
  protected comm_comp_comul : (TensorProduct.comm R A A).comp comul = comul

variable [IsCocomm R A]

variable (R A) in
/-
**Coalgebra.comm_comp_comul** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra`。
形式化陈述：∀ (R : Type u) (A : Type v) [inst : CommSemiring R] [inst_1 : AddCommMonoi
d A] [inst_2 : _root_.Module R A]   [inst_3 : Coalgebra R A] [Coalgebra.IsCocomm
 R A],   ↑(TensorProduct.comm R A A) ∘ₗ CoalgebraStruct.comul = CoalgebraStruct.
comul
参数：R : Type u；A : Type v；TensorProduct.comm R A A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Coalgebra.IsCocomm.comm_comp_comul`：∀ {R : Type u} {A : Type v} {inst : 
CommSemiring R} {inst_1 : AddCommMonoid A} {inst_2 : _root_.Module R A}   {inst_
3 : Coalgebra R A} [self…
-/
@[simp] lemma comm_comp_comul : (TensorProduct.comm R A A).comp comul = comul :=
  IsCocomm.comm_comp_comul

variable (R) in
/-
**Coalgebra.comm_comul** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra`。
形式化陈述：∀ (R : Type u) {A : Type v} [inst : CommSemiring R] [inst_1 : AddCommMonoi
d A] [inst_2 : _root_.Module R A]   [inst_3 : Coalgebra R A] [Coalgebra.IsCocomm
 R A] (a : A),   (TensorProduct.comm R A A) (CoalgebraStruct.comul a) = Coalgebr
aStruct.comul a
参数：R : Type u；a : A；TensorProduct.comm R A A；CoalgebraStruct.comul a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Coalgebra.comm_comp_comul`：∀ (R : Type u) (A : Type v) [inst : CommSemir
ing R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3 : Coalg
ebra R A] [Coal…
-/
@[simp] lemma comm_comul (a : A) : TensorProduct.comm R A A (comul a) = comul a :=
  congr($(comm_comp_comul R A) a)

end Coalgebra

open Coalgebra

namespace CommSemiring
variable (R : Type u) [CommSemiring R]

/-- Every commutative (semi)ring is a coalgebra over itself, with `Δ r = 1 ⊗ₜ r`. -/
/-
**CommSemiring.toCoalgebra** 是 Mathlib 中的一个实例，位于命名空间 `CommSemiring`。
形式化陈述：toCoalgebra : Coalgebra R R where comul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every commutative (semi)ring is a coalgebra over itself, with `Δ r = 1 ⊗ₜ r`.
-/
instance toCoalgebra : Coalgebra R R where
  comul := (TensorProduct.mk R R R) 1
  counit := .id
  coassoc := rfl
  rTensor_counit_comp_comul := by ext; rfl
  lTensor_counit_comp_comul := by ext; rfl

@[simp]
/-
**CommSemiring.comul_apply** 是 Mathlib 中的一个定理，位于命名空间 `CommSemiring`。
形式化陈述：comul_apply (r : R) : comul r = 1 otimesₜ[R] r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comul_apply (r : R) : comul r = 1 ⊗ₜ[R] r := rfl

@[simp]
/-
**CommSemiring.counit_apply** 是 Mathlib 中的一个定理，位于命名空间 `CommSemiring`。
形式化陈述：counit_apply (r : R) : counit r = r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem counit_apply (r : R) : counit r = r := rfl
/-
**CommSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `CommSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCocomm R R where comm_comp_comul := by ext; simp

end CommSemiring

namespace Prod
variable (R : Type u) (A : Type v) (B : Type w)
variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
variable [Coalgebra R A] [Coalgebra R B]

open LinearMap

/-
**Prod.instCoalgebraStruct** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instCoalgebraStruct : CoalgebraStruct R (A × B) where comul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoalgebraStruct : CoalgebraStruct R (A × B) where
  comul := .coprod
    (TensorProduct.map (.inl R A B) (.inl R A B) ∘ₗ comul)
    (TensorProduct.map (.inr R A B) (.inr R A B) ∘ₗ comul)
  counit := .coprod counit counit

@[simp]
/-
**Prod.comul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：comul_apply (r : A × B) : comul r = TensorProduct.map (.inl R A B) (.inl R
 A B) (comul r.1) + TensorProduct.map (.inr R A B) (.inr R A B) (comul r.2)
参数：r : A × B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comul_apply (r : A × B) :
    comul r =
      TensorProduct.map (.inl R A B) (.inl R A B) (comul r.1) +
      TensorProduct.map (.inr R A B) (.inr R A B) (comul r.2) := rfl

@[simp]
/-
**Prod.counit_apply** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：counit_apply (r : A × B) : (counit r : R) = counit r.1 + counit r.2
参数：r : A × B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem counit_apply (r : A × B) : (counit r : R) = counit r.1 + counit r.2 := rfl
/-
**Prod.comul_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：comul_comp_inl : comul ∘ₗ inl R A B = TensorProduct.map (.inl R A B) (.inl
 R A B) ∘ₗ comul
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comul_comp_inl :
    comul ∘ₗ inl R A B = TensorProduct.map (.inl R A B) (.inl R A B) ∘ₗ comul := by
  ext; simp
/-
**Prod.comul_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：comul_comp_inr : comul ∘ₗ inr R A B = TensorProduct.map (.inr R A B) (.inr
 R A B) ∘ₗ comul
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comul_comp_inr :
    comul ∘ₗ inr R A B = TensorProduct.map (.inr R A B) (.inr R A B) ∘ₗ comul := by
  ext; simp
/-
**Prod.comul_comp_fst** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：comul_comp_fst : comul ∘ₗ .fst R A B = TensorProduct.map (.fst R A B) (.fs
t R A B) ∘ₗ comul
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.prod_ext`：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl 
_ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f 
= g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearMap.fst_comp_inl`：∀ (R : Type u) (M : Type v) (M₂ : Type w) [inst 
: Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 :
 _root_.Modu…
· 使用定理 `LinearMap.comp_id`：comp_id : f.comp id = f
· 使用定理 `Prod.comul_comp_inl`：comul_comp_inl : comul ∘ₗ inl R A B = TensorProduct
.map (.inl R A B) (.inl R A B) ∘ₗ comul
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.map_comp`：map_comp (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂
₃] N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) : map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁)
 = (map f₂ g…
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
· 使用定理 `LinearMap.id_comp`：id_comp : id.comp f = f
· 使用定理 `LinearMap.fst_comp_inr`：∀ (R : Type u) (M : Type v) (M₂ : Type w) [inst 
: Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 :
 _root_.Modu…
· 使用定理 `LinearMap.comp_zero`：comp_zero (g : M₂ ->ₛₗ[σ₂₃] M₃) : (g.comp (0 : M ->
ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = 0
· 使用定理 `Prod.comul_comp_inr`：comul_comp_inr : comul ∘ₗ inr R A B = TensorProduct
.map (.inr R A B) (.inr R A B) ∘ₗ comul
· 使用定理 `TensorProduct.map_zero_left`：map_zero_left (g : N ->ₛₗ[σ₁₂] N₂) : map (0
 : M ->ₛₗ[σ₁₂] M₂) g = 0
· 使用定理 `LinearMap.zero_comp`：zero_comp (f : M ->ₛₗ[σ₁₂] M₂) : ((0 : M₂ ->ₛₗ[σ₂₃]
 M₃).comp f : M ->ₛₗ[σ₁₃] M₃) = 0
-/
theorem comul_comp_fst :
    comul ∘ₗ .fst R A B = TensorProduct.map (.fst R A B) (.fst R A B) ∘ₗ comul := by
  ext : 1
  · rw [comp_assoc, fst_comp_inl, comp_id, comp_assoc, comul_comp_inl, ← comp_assoc,
      ← TensorProduct.map_comp, fst_comp_inl, TensorProduct.map_id, id_comp]
  · rw [comp_assoc, fst_comp_inr, comp_zero, comp_assoc, comul_comp_inr, ← comp_assoc,
      ← TensorProduct.map_comp, fst_comp_inr, TensorProduct.map_zero_left, zero_comp]
/-
**Prod.comul_comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：comul_comp_snd : comul ∘ₗ .snd R A B = TensorProduct.map (.snd R A B) (.sn
d R A B) ∘ₗ comul
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.prod_ext`：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl 
_ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f 
= g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearMap.snd_comp_inl`：∀ (R : Type u) (M : Type v) (M₂ : Type w) [inst 
: Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 :
 _root_.Modu…
· 使用定理 `LinearMap.comp_zero`：comp_zero (g : M₂ ->ₛₗ[σ₂₃] M₃) : (g.comp (0 : M ->
ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = 0
· 使用定理 `Prod.comul_comp_inl`：comul_comp_inl : comul ∘ₗ inl R A B = TensorProduct
.map (.inl R A B) (.inl R A B) ∘ₗ comul
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.map_comp`：map_comp (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂
₃] N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) : map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁)
 = (map f₂ g…
· 使用定理 `TensorProduct.map_zero_left`：map_zero_left (g : N ->ₛₗ[σ₁₂] N₂) : map (0
 : M ->ₛₗ[σ₁₂] M₂) g = 0
· 使用定理 `LinearMap.zero_comp`：zero_comp (f : M ->ₛₗ[σ₁₂] M₂) : ((0 : M₂ ->ₛₗ[σ₂₃]
 M₃).comp f : M ->ₛₗ[σ₁₃] M₃) = 0
· 使用定理 `LinearMap.snd_comp_inr`：∀ (R : Type u) (M : Type v) (M₂ : Type w) [inst 
: Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 :
 _root_.Modu…
· 使用定理 `LinearMap.comp_id`：comp_id : f.comp id = f
· 使用定理 `Prod.comul_comp_inr`：comul_comp_inr : comul ∘ₗ inr R A B = TensorProduct
.map (.inr R A B) (.inr R A B) ∘ₗ comul
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
· 使用定理 `LinearMap.id_comp`：id_comp : id.comp f = f
-/
theorem comul_comp_snd :
    comul ∘ₗ .snd R A B = TensorProduct.map (.snd R A B) (.snd R A B) ∘ₗ comul := by
  ext : 1
  · rw [comp_assoc, snd_comp_inl, comp_zero, comp_assoc, comul_comp_inl, ← comp_assoc,
      ← TensorProduct.map_comp, snd_comp_inl, TensorProduct.map_zero_left, zero_comp]
  · rw [comp_assoc, snd_comp_inr, comp_id, comp_assoc, comul_comp_inr, ← comp_assoc,
      ← TensorProduct.map_comp, snd_comp_inr, TensorProduct.map_id, id_comp]
/-
**Prod.counit_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ (R : Type u) (A : Type v) (B : Type w) [inst : CommSemiring R] [inst_1 :
 AddCommMonoid A] [inst_2 : AddCommMonoid B]   [inst_3 : _root_.Module R A] [ins
t_4 : _root_.Module R B] [inst_5 : Coalgebra R A] [inst_6 : Coalgebra R B],   Co
algebraStruct.counit ∘ₗ LinearMap.inr R A B = CoalgebraStruct.counit
参数：R : Type u；A : Type v；B : Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem counit_comp_inr : counit ∘ₗ inr R A B = counit := by ext; simp
/-
**Prod.counit_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ (R : Type u) (A : Type v) (B : Type w) [inst : CommSemiring R] [inst_1 :
 AddCommMonoid A] [inst_2 : AddCommMonoid B]   [inst_3 : _root_.Module R A] [ins
t_4 : _root_.Module R B] [inst_5 : Coalgebra R A] [inst_6 : Coalgebra R B],   Co
algebraStruct.counit ∘ₗ LinearMap.inl R A B = CoalgebraStruct.counit
参数：R : Type u；A : Type v；B : Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem counit_comp_inl : counit ∘ₗ inl R A B = counit := by ext; simp
/-
**Prod.instCoalgebra** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instCoalgebra : Coalgebra R (A × B) where rTensor_counit_comp_comul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoalgebra : Coalgebra R (A × B) where
  rTensor_counit_comp_comul := by
    ext : 1
    · rw [comp_assoc, comul_comp_inl, ← comp_assoc, rTensor_comp_map, counit_comp_inl,
        ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
    · rw [comp_assoc, comul_comp_inr, ← comp_assoc, rTensor_comp_map, counit_comp_inr,
        ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    · rw [comp_assoc, comul_comp_inl, ← comp_assoc, lTensor_comp_map, counit_comp_inl,
        ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
    · rw [comp_assoc, comul_comp_inr, ← comp_assoc, lTensor_comp_map, counit_comp_inr,
        ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
  coassoc := by
    dsimp +instances only [instCoalgebraStruct]
    ext x : 2 <;> dsimp only [comp_apply, LinearEquiv.coe_coe, coe_inl, coe_inr, coprod_apply]
    · simp only [map_zero, add_zero]
      simp_rw [← comp_apply, ← comp_assoc, rTensor_comp_map, lTensor_comp_map, coprod_inl,
        ← map_comp_rTensor, ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq, comp_apply, LinearEquiv.coe_coe]
    · simp only [map_zero, zero_add]
      simp_rw [← comp_apply, ← comp_assoc, rTensor_comp_map, lTensor_comp_map, coprod_inr,
        ← map_comp_rTensor, ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq, comp_apply, LinearEquiv.coe_coe]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCocomm R A] [IsCocomm R B] : IsCocomm R (A × B) where
  comm_comp_comul := by ext <;> simp [← TensorProduct.map_comm]

end Prod

namespace DFinsupp
variable (R : Type u) (ι : Type v) (A : ι → Type w)
variable [DecidableEq ι]
variable [CommSemiring R] [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]

open LinearMap

section coalgebraStruct
variable [∀ i, CoalgebraStruct R (A i)]

/-
**DFinsupp.instCoalgebraStruct** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：instCoalgebraStruct : CoalgebraStruct R (Π₀ i, A i) where comul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoalgebraStruct : CoalgebraStruct R (Π₀ i, A i) where
  comul := DFinsupp.lsum R fun i =>
    TensorProduct.map (DFinsupp.lsingle i) (DFinsupp.lsingle i) ∘ₗ comul
  counit := DFinsupp.lsum R fun _ => counit

@[simp]
/-
**DFinsupp.comul_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：comul_single (i : ι) (a : A i) : comul (R
参数：i : ι；a : A i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.lsum_single`：lsum_single [Semiring S] [Module S N] [SMulCommCla
ss R S N] (F : forall i, M i ->ₗ[R] N) (i) (x : M i) : lsum S F (single i x) = F
 i x
-/
theorem comul_single (i : ι) (a : A i) :
    comul (R := R) (DFinsupp.single i a) =
      (TensorProduct.map (DFinsupp.lsingle i) (DFinsupp.lsingle i) : _ →ₗ[R] _) (comul a) :=
  lsum_single _ _ _ _

@[simp]
/-
**DFinsupp.counit_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：counit_single (i : ι) (a : A i) : counit (DFinsupp.single i a) = counit (R
参数：i : ι；a : A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.lsum_single`：lsum_single [Semiring S] [Module S N] [SMulCommCla
ss R S N] (F : forall i, M i ->ₗ[R] N) (i) (x : M i) : lsum S F (single i x) = F
 i x
-/
theorem counit_single (i : ι) (a : A i) : counit (DFinsupp.single i a) = counit (R := R) a :=
  lsum_single _ _ _ _
/-
**DFinsupp.comul_comp_lsingle** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：comul_comp_lsingle (i : ι) : comul ∘ₗ (lsingle i : A i ->ₗ[R] _) = TensorP
roduct.map (lsingle i) (lsingle i) ∘ₗ comul
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.comul_single`：comul_single (i : ι) (a : A i) : comul (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comul_comp_lsingle (i : ι) :
    comul ∘ₗ (lsingle i : A i →ₗ[R] _) = TensorProduct.map (lsingle i) (lsingle i) ∘ₗ comul := by
  ext; simp
/-
**DFinsupp.comul_comp_lapply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：comul_comp_lapply (i : ι) : comul ∘ₗ (lapply i : _ ->ₗ[R] A i) = TensorPro
duct.map (lapply i) (lapply i) ∘ₗ comul
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (Π₀ i, M i) ->ₗ[R] N⦄ (h : forall i
, φ.comp (lsingle i) = ψ.comp (lsingle i)) : φ = ψ
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `DFinsupp.comul_single`：comul_single (i : ι) (a : A i) : comul (R
· 使用定理 `TensorProduct.map_map`：map_map (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃]
 N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) (x : M otimes[R] N) : map f₂ g₂
 (map f₁ g₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.lapply_comp_lsingle_same`：lapply_comp_lsingle_same [DecidableEq
 ι] (i : ι) : lapply i ∘ₗ lsingle i = (.id : M i ->ₗ[R] M i)
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
· 使用定理 `DFinsupp.lapply_comp_lsingle_of_ne`：lapply_comp_lsingle_of_ne [Decidable
Eq ι] (i i' : ι) (h : i != i') : lapply i ∘ₗ lsingle i' = (0 : M i' ->ₗ[R] M i)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `TensorProduct.map_zero_right`：map_zero_right (f : M ->ₛₗ[σ₁₂] M₂) : map 
f (0 : N ->ₛₗ[σ₁₂] N₂) = 0
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
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
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem comul_comp_lapply (i : ι) :
    comul ∘ₗ (lapply i : _ →ₗ[R] A i) = TensorProduct.map (lapply i) (lapply i) ∘ₗ comul := by
  ext j
  have := eq_or_ne i j
  aesop (add simp [TensorProduct.map_map, proj_comp_single, diag])
/-
**DFinsupp.counit_comp_lsingle** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ (R : Type u) (ι : Type v) (A : ι → Type w) [inst : DecidableEq ι] [inst_
1 : CommSemiring R]   [inst_2 : (i : ι) → AddCommMonoid (A i)] [inst_3 : (i : ι)
 → _root_.Module R (A i)]   [inst_4 : (i : ι) → CoalgebraStruct R (A i)] (i : ι)
,   CoalgebraStruct.counit ∘ₗ DFinsupp.lsingle i = CoalgebraStruct.counit
参数：R : Type u；ι : Type v；A : ι → Type w；i : ι；A i；i : ι；A i；i : ι；A i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.counit_single`：counit_single (i : ι) (a : A i) : counit (DFinsu
pp.single i a) = counit (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem counit_comp_lsingle (i : ι) : counit ∘ₗ (lsingle i : A i →ₗ[R] _) = counit := by
  ext; simp

end coalgebraStruct

variable [∀ i, Coalgebra R (A i)]

/-- The `R`-module whose elements are dependent functions `(i : ι) → A i` which are zero on all but
finitely many elements of `ι` has a coalgebra structure.

The coproduct `Δ` is given by `Δ(fᵢ a) = fᵢ a₁ ⊗ fᵢ a₂` where `Δ(a) = a₁ ⊗ a₂` and the counit `ε`
by `ε(fᵢ a) = ε(a)`, where `fᵢ a` is the function sending `i` to `a` and all other elements of `ι`
to zero. -/
/-
**DFinsupp.instCoalgebra** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：instCoalgebra : Coalgebra R (Π₀ i, A i) where rTensor_counit_comp_comul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-module whose elements are dependent functions `(i : ι) → A i` which are 
zero on all but
finitely many elements of `ι` has a coalgebra structure.

The coproduct `Δ` is given by `Δ(fᵢ a) = fᵢ a₁ ⊗ fᵢ a₂` where `Δ(a) = a₁ ⊗ a₂` a
nd the counit `ε`
by `ε(fᵢ a) = ε(a)`, where `fᵢ a` is the function sending `i` to `a` and all oth
er elements of `ι`
to zero.
-/
instance instCoalgebra : Coalgebra R (Π₀ i, A i) where
  rTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, rTensor_comp_map, counit_comp_lsingle,
      ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, lTensor_comp_map, counit_comp_lsingle,
      ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
  coassoc := by
    ext i : 1
    simp_rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, lTensor_comp_map, comul_comp_lsingle,
      comp_assoc, ← comp_assoc comul, rTensor_comp_map, comul_comp_lsingle, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc comul, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq]
/-
**DFinsupp.instIsCocomm** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：instIsCocomm [forall i, IsCocomm R (A i)] : IsCocomm R (Π₀ i, A i) where c
omm_comp_comul
参数：A i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (Π₀ i, M i) ->ₗ[R] N⦄ (h : forall i
, φ.comp (lsingle i) = ψ.comp (lsingle i)) : φ = ψ
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.comul_single`：comul_single (i : ι) (a : A i) : comul (R
· 使用定理 `Coalgebra.comm_comul`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R
] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3 : Coalgebra 
R A] [Coal…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instIsCocomm [∀ i, IsCocomm R (A i)] : IsCocomm R (Π₀ i, A i) where
  comm_comp_comul := by ext; simp [← TensorProduct.map_comm]

end DFinsupp

namespace Finsupp
variable (R : Type u) (ι : Type v) (A : Type w)
variable [CommSemiring R] [AddCommMonoid A] [Module R A]

open LinearMap

section coalgebraStruct
variable [CoalgebraStruct R A]

/-
**Finsupp.instCoalgebraStruct** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instCoalgebraStruct : CoalgebraStruct R (ι ->₀ A) where comul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instCoalgebraStruct : CoalgebraStruct R (ι →₀ A) where
  comul := Finsupp.lsum R fun i =>
    TensorProduct.map (Finsupp.lsingle i) (Finsupp.lsingle i) ∘ₗ comul
  counit := Finsupp.lsum R fun _ => counit

@[simp]
/-
**Finsupp.comul_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comul_single (i : ι) (a : A) : comul (R
参数：i : ι；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lsum_single`：lsum_single (f : α -> M ->ₛₗ[σ] N) (i : α) (m : M) 
: Finsupp.lsum S f (Finsupp.single i m) = f i m
-/
theorem comul_single (i : ι) (a : A) :
    comul (R := R) (Finsupp.single i a) =
      (TensorProduct.map (Finsupp.lsingle i) (Finsupp.lsingle i) : _ →ₗ[R] _) (comul a) :=
  lsum_single _ _ _ _

@[simp]
/-
**Finsupp.counit_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：counit_single (i : ι) (a : A) : counit (Finsupp.single i a) = counit (R
参数：i : ι；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lsum_single`：lsum_single (f : α -> M ->ₛₗ[σ] N) (i : α) (m : M) 
: Finsupp.lsum S f (Finsupp.single i m) = f i m
-/
theorem counit_single (i : ι) (a : A) : counit (Finsupp.single i a) = counit (R := R) a :=
  lsum_single _ _ _ _
/-
**Finsupp.comul_comp_lsingle** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comul_comp_lsingle (i : ι) : comul ∘ₗ (lsingle i : A ->ₗ[R] _) = TensorPro
duct.map (lsingle i) (lsingle i) ∘ₗ comul
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.comul_single`：comul_single (i : ι) (a : A) : comul (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comul_comp_lsingle (i : ι) :
    comul ∘ₗ (lsingle i : A →ₗ[R] _) = TensorProduct.map (lsingle i) (lsingle i) ∘ₗ comul := by
  ext; simp
/-
**Finsupp.comul_comp_lapply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comul_comp_lapply (i : ι) : comul ∘ₗ (lapply i : _ ->ₗ[R] A) = TensorProdu
ct.map (lapply i) (lapply i) ∘ₗ comul
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.comul_single`：comul_single (i : ι) (a : A) : comul (R
· 使用定理 `TensorProduct.map_map`：map_map (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃]
 N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) (x : M otimes[R] N) : map f₂ g₂
 (map f₁ g₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.lapply_comp_lsingle_same`：lapply_comp_lsingle_same (a : α) : lap
ply a ∘ₗ lsingle a = (.id : M ->ₗ[R] M)
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
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
· 使用定理 `Finsupp.lapply_comp_lsingle_of_ne`：lapply_comp_lsingle_of_ne (a a' : α) 
(h : a != a') : lapply a ∘ₗ lsingle a' = (0 : M ->ₗ[R] M)
· 使用定理 `TensorProduct.map_zero_right`：map_zero_right (f : M ->ₛₗ[σ₁₂] M₂) : map 
f (0 : N ->ₛₗ[σ₁₂] N₂) = 0
-/
theorem comul_comp_lapply (i : ι) :
    comul ∘ₗ (lapply i : _ →ₗ[R] A) = TensorProduct.map (lapply i) (lapply i) ∘ₗ comul := by
  ext j; have := eq_or_ne i j
  aesop (add simp [TensorProduct.map_map, proj_comp_single, diag])
/-
**Finsupp.counit_comp_lsingle** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ (R : Type u) (ι : Type v) (A : Type w) [inst : CommSemiring R] [inst_1 :
 AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3 : CoalgebraStruct R A] 
(i : ι), CoalgebraStruct.counit ∘ₗ Finsupp.lsingle i = CoalgebraStruct.counit
参数：R : Type u；ι : Type v；A : Type w；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.counit_single`：counit_single (i : ι) (a : A) : counit (Finsupp.s
ingle i a) = counit (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem counit_comp_lsingle (i : ι) : counit ∘ₗ (lsingle i : A →ₗ[R] _) = counit := by
  ext; simp

end coalgebraStruct

variable [Coalgebra R A]

/-- The `R`-module whose elements are functions `ι → A` which are zero on all but finitely many
elements of `ι` has a coalgebra structure. The coproduct `Δ` is given by `Δ(fᵢ a) = fᵢ a₁ ⊗ fᵢ a₂`
where `Δ(a) = a₁ ⊗ a₂` and the counit `ε` by `ε(fᵢ a) = ε(a)`, where `fᵢ a` is the function sending
`i` to `a` and all other elements of `ι` to zero. -/
/-
**Finsupp.instCoalgebra** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instCoalgebra : Coalgebra R (ι ->₀ A) where rTensor_counit_comp_comul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-module whose elements are functions `ι → A` which are zero on all but fi
nitely many
elements of `ι` has a coalgebra structure. The coproduct `Δ` is given by `Δ(fᵢ a
) = fᵢ a₁ ⊗ fᵢ a₂`
where `Δ(a) = a₁ ⊗ a₂` and the counit `ε` by `ε(fᵢ a) = ε(a)`, where `fᵢ a` is t
he function sending
`i` to `a` and all other elements of `ι` to zero.
-/
noncomputable instance instCoalgebra : Coalgebra R (ι →₀ A) where
  rTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, rTensor_comp_map, counit_comp_lsingle,
      ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, lTensor_comp_map, counit_comp_lsingle,
      ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
  coassoc := by
    ext i : 1
    simp_rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, lTensor_comp_map, comul_comp_lsingle,
      comp_assoc, ← comp_assoc comul, rTensor_comp_map, comul_comp_lsingle, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc comul, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq]
/-
**Finsupp.instIsCocomm** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instIsCocomm [IsCocomm R A] : IsCocomm R (ι ->₀ A) where comm_comp_comul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.comul_single`：comul_single (i : ι) (a : A) : comul (R
· 使用定理 `Coalgebra.comm_comul`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R
] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3 : Coalgebra 
R A] [Coal…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instIsCocomm [IsCocomm R A] : IsCocomm R (ι →₀ A) where
  comm_comp_comul := by ext; simp [← TensorProduct.map_comm]

end Finsupp

namespace Pi
variable {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n]
  {A : n → Type*} [Π i, AddCommMonoid (A i)] [Π i, Module R (A i)]

open TensorProduct LinearMap

section coalgebraStruct
variable [Π i, CoalgebraStruct R (A i)]

/-
**Pi.instCoalgebraStruct** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instCoalgebraStruct : CoalgebraStruct R (Π i, A i) where comul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoalgebraStruct : CoalgebraStruct R (Π i, A i) where
  comul := .lsum R _ R fun i ↦ map (.single R _ i) (.single R _ i) ∘ₗ comul
  counit := .lsum R _ R fun _ ↦ counit
/-
**Pi.comul_single** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (i : n) → AddCommMono
id (A i)] [inst_4 : (i : n) → _root_.Module R (A i)]   [inst_5 : (i : n) → Coalg
ebraStruct R (A i)] (i : n) (a : A i),   CoalgebraStruct.comul (Pi.single i a) =
     (TensorProduct.map (LinearMap.single R A i) (LinearMap.single R A i)) (Coal
gebraStruct.comul a)
参数：i : n；A i；i : n；A i；i : n；A i；i : n；a : A i；Pi.single i a；TensorProduct.map (
LinearMap.single R A i) (LinearMap.single R A i)；CoalgebraStruct.comul a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.lsum_piSingle`：lsum_piSingle (S) [AddCommMonoid M] [Module R M
] [Fintype ι] [Semiring S] [Module S M] [SMulCommClass R S M] (f : (i : ι) -> φ 
i ->ₗ[R] M) (…
-/
@[simp] theorem comul_single (i : n) (a : A i) :
    comul (single i a) = map (.single R _ i) (.single R _ i) (comul a) :=
  lsum_piSingle _ _ _ _ _ _
/-
**Pi.counit_single** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (i : n) → AddCommMono
id (A i)] [inst_4 : (i : n) → _root_.Module R (A i)]   [inst_5 : (i : n) → Coalg
ebraStruct R (A i)] (i : n) (a : A i),   CoalgebraStruct.counit (Pi.single i a) 
= CoalgebraStruct.counit a
参数：i : n；A i；i : n；A i；i : n；A i；i : n；a : A i；Pi.single i a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.lsum_piSingle`：lsum_piSingle (S) [AddCommMonoid M] [Module R M
] [Fintype ι] [Semiring S] [Module S M] [SMulCommClass R S M] (f : (i : ι) -> φ 
i ->ₗ[R] M) (…
-/
@[simp] theorem counit_single (i : n) (a : A i) : counit (single i a) = counit (R := R) a :=
  lsum_piSingle _ _ _ _ _ _
/-
**Pi.comul_comp_single** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：comul_comp_single (i : n) : comul ∘ₗ .single R _ i = map (.single R A i) (
.single R A i) ∘ₗ comul
参数：i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.comul_single`：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R]
 [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (i
 : n)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comul_comp_single (i : n) :
    comul ∘ₗ .single R _ i = map (.single R A i) (.single R A i) ∘ₗ comul := by
  ext; simp
/-
**Pi.comul_comp_proj** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：comul_comp_proj (i : n) : comul ∘ₗ (proj i : (Π i, A i) ->ₗ[R] A i) = map 
(proj i) (proj i) ∘ₗ comul
参数：i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Pi.comul_single`：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R]
 [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (i
 : n)…
· 使用定理 `TensorProduct.map_map`：map_map (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃]
 N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) (x : M otimes[R] N) : map f₂ g₂
 (map f₁ g₁…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.proj_comp_single`：proj_comp_single (i j : ι) : (proj i).comp (
single R φ j) = diag j i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
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
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `TensorProduct.map_zero_right`：map_zero_right (f : M ->ₛₗ[σ₁₂] M₂) : map 
f (0 : N ->ₛₗ[σ₁₂] N₂) = 0
-/
theorem comul_comp_proj (i : n) :
    comul ∘ₗ (proj i : (Π i, A i) →ₗ[R] A i) = map (proj i) (proj i) ∘ₗ comul := by
  ext j; have := eq_or_ne i j
  aesop (add simp [map_map, proj_comp_single, diag])
/-
**Pi.counit_comp_single** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (i : n) → AddCommMono
id (A i)] [inst_4 : (i : n) → _root_.Module R (A i)]   [inst_5 : (i : n) → Coalg
ebraStruct R (A i)] (i : n),   CoalgebraStruct.counit ∘ₗ LinearMap.single R A i 
= CoalgebraStruct.counit
参数：i : n；A i；i : n；A i；i : n；A i；i : n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.counit_single`：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R
] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (
i : n)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem counit_comp_single (i : n) : counit ∘ₗ .single R A i = counit := by ext; simp
/-
**Pi.counit_comp_dFinsuppCoeFnLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：counit_comp_dFinsuppCoeFnLinearMap : counit (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFinsupp.sum_single`：sum_single [forall i, AddCommMonoid (β i)] [forall 
(i) (x : β i), Decidable (x != 0)] {f : Π₀ i, β i} : f.sum single = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DFinsupp.sum_eq_sum_fintype`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v
} [inst : DecidableEq ι] [inst_1 : Fintype ι] [inst_2 : (i : ι) → Zero (β i)]   
[inst_3 : (i : ι)…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.single_zero`：single_zero (i) : (single i 0 : Π₀ i, β i) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `DFinsupp.equivFunOnFintype_apply`：∀ {ι : Type u} {β : ι → Type v} [inst 
: (i : ι) → Zero (β i)] [inst_1 : Fintype ι] (a : Π₀ (i : ι), β i) (a_1 : ι),   
DFinsupp.equivFunOnFin…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Pi.counit_single`：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R
] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (
i : n)…
· 使用定理 `DFinsupp.counit_single`：counit_single (i : ι) (a : A i) : counit (DFinsu
pp.single i a) = counit (R
-/
theorem counit_comp_dFinsuppCoeFnLinearMap :
    counit (R := R) (A := Π i, A i) ∘ₗ DFinsupp.coeFnLinearMap _ = counit := by
  apply LinearMap.ext fun x ↦ ?_
  have (i : n) (x : A i) : Decidable (x ≠ 0) := Classical.propDecidable _
  rw [← DFinsupp.sum_single (f := x)]
  simp [DFinsupp.single_eq_pi_single]
/-
**Pi.counit_coe_dFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (i : n) → AddCommMono
id (A i)] [inst_4 : (i : n) → _root_.Module R (A i)]   [inst_5 : (i : n) → Coalg
ebraStruct R (A i)] (x : Π₀ (i : n), A i),   CoalgebraStruct.counit ⇑x = Coalgeb
raStruct.counit x
参数：i : n；A i；i : n；A i；i : n；A i；x : Π₀ (i : n), A i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.counit_comp_dFinsuppCoeFnLinearMap`：counit_comp_dFinsuppCoeFnLinearMa
p : counit (R
-/
@[simp] theorem counit_coe_dFinsupp (x : Π₀ i, A i) :
    counit (R := R) ⇑x = counit x := congr($counit_comp_dFinsuppCoeFnLinearMap x)

open DFinsupp in
/-
**Pi.comul_comp_dFinsuppCoeFnLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：comul_comp_dFinsuppCoeFnLinearMap : comul (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFinsupp.sum_single`：sum_single [forall i, AddCommMonoid (β i)] [forall 
(i) (x : β i), Decidable (x != 0)] {f : Π₀ i, β i} : f.sum single = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFinsupp.sum_eq_sum_fintype`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v
} [inst : DecidableEq ι] [inst_1 : Fintype ι] [inst_2 : (i : ι) → Zero (β i)]   
[inst_3 : (i : ι)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.single_zero`：single_zero (i) : (single i 0 : Π₀ i, β i) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `DFinsupp.equivFunOnFintype_apply`：∀ {ι : Type u} {β : ι → Type v} [inst 
: (i : ι) → Zero (β i)] [inst_1 : Fintype ι] (a : Π₀ (i : ι), β i) (a_1 : ι),   
DFinsupp.equivFunOnFin…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Pi.comul_single`：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R]
 [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (i
 : n)…
· 使用定理 `DFinsupp.comul_single`：comul_single (i : ι) (a : A i) : comul (R
· 使用定理 `TensorProduct.map_map`：map_map (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃]
 N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) (x : M otimes[R] N) : map f₂ g₂
 (map f₁ g₁…
-/
theorem comul_comp_dFinsuppCoeFnLinearMap :
    comul (R := R) (A := Π i, A i) ∘ₗ coeFnLinearMap _ =
      map (coeFnLinearMap _) (coeFnLinearMap _) ∘ₗ comul := by
  apply LinearMap.ext fun x ↦ ?_
  have (i : n) (x : A i) : Decidable (x ≠ 0) := Classical.propDecidable _
  rw [← DFinsupp.sum_single (f := x)]
  aesop (add simp [map_map, DFinsupp.single_eq_pi_single])

open DFinsupp in
/-
**Pi.comul_coe_dFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (i : n) → AddCommMono
id (A i)] [inst_4 : (i : n) → _root_.Module R (A i)]   [inst_5 : (i : n) → Coalg
ebraStruct R (A i)] (x : Π₀ (i : n), A i),   CoalgebraStruct.comul ⇑x =     (Ten
sorProduct.map (DFinsupp.coeFnLinearMap R) (DFinsupp.coeFnLinearMap R)) (Coalgeb
raStruct.comul x)
参数：i : n；A i；i : n；A i；i : n；A i；x : Π₀ (i : n), A i；TensorProduct.map (DFinsupp
.coeFnLinearMap R) (DFinsupp.coeFnLinearMap R)；CoalgebraStruct.comul x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.comul_comp_dFinsuppCoeFnLinearMap`：comul_comp_dFinsuppCoeFnLinearMap 
: comul (R
-/
@[simp] theorem comul_coe_dFinsupp (x : Π₀ i, A i) :
    comul (R := R) ⇑x = map (coeFnLinearMap _) (coeFnLinearMap _) (comul x) :=
  congr($comul_comp_dFinsuppCoeFnLinearMap x)

variable {M : Type*} [AddCommMonoid M] [Module R M] [CoalgebraStruct R M]
/-
**Pi.counit_comp_finsuppLcoeFun** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：counit_comp_finsuppLcoeFun : counit (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.univ_sum_single`：univ_sum_single [Fintype α] [AddCommMonoid M] (
f : α ->₀ M) : ∑ a : α, single a (f a) = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.single_eq_pi_single`：single_eq_pi_single [DecidableEq α] (a : α)
 (b : M) : ⇑(single a b) = Pi.single a b
· 使用定理 `Pi.counit_single`：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R
] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (
i : n)…
· 使用定理 `Finsupp.counit_single`：counit_single (i : ι) (a : A) : counit (Finsupp.s
ingle i a) = counit (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem counit_comp_finsuppLcoeFun :
    counit (R := R) (A := n → M) ∘ₗ Finsupp.lcoeFun = counit := by
  apply LinearMap.ext fun x ↦ ?_
  rw [← Finsupp.univ_sum_single x]
  simp [-Finsupp.univ_sum_single, Finsupp.lcoeFun, Finsupp.single_eq_pi_single]
/-
**Pi.counit_coe_finsupp** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n] {M : Type u_4}   [inst_3 : AddCommMonoid M] [inst_4 
: _root_.Module R M] [inst_5 : CoalgebraStruct R M] (x : n →₀ M),   CoalgebraStr
uct.counit ⇑x = CoalgebraStruct.counit x
参数：x : n →₀ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.counit_comp_finsuppLcoeFun`：counit_comp_finsuppLcoeFun : counit (R
-/
@[simp] theorem counit_coe_finsupp (x : n →₀ M) :
    counit (R := R) ⇑x = counit x := congr($counit_comp_finsuppLcoeFun x)

open Finsupp in
/-
**Pi.comul_comp_finsuppLcoeFun** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：comul_comp_finsuppLcoeFun : comul (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.univ_sum_single`：univ_sum_single [Fintype α] [AddCommMonoid M] (
f : α ->₀ M) : ∑ a : α, single a (f a) = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.single_eq_pi_single`：single_eq_pi_single [DecidableEq α] (a : α)
 (b : M) : ⇑(single a b) = Pi.single a b
· 使用定理 `Pi.comul_single`：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R]
 [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (i
 : n)…
· 使用定理 `Finsupp.comul_single`：comul_single (i : ι) (a : A) : comul (R
· 使用定理 `TensorProduct.map_map`：map_map (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃]
 N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) (x : M otimes[R] N) : map f₂ g₂
 (map f₁ g₁…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.lcoeFun_comp_lsingle`：∀ {α : Type u_1} {M : Type u_2} {R : Type 
u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R 
M] [inst_3 : Decid…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comul_comp_finsuppLcoeFun :
    comul (R := R) (A := n → M) ∘ₗ lcoeFun = map lcoeFun lcoeFun ∘ₗ comul := by
  apply LinearMap.ext fun x ↦ ?_
  rw [← Finsupp.univ_sum_single x]
  simp [-univ_sum_single, single_eq_pi_single, map_map]

open Finsupp in
/-
**Pi.comul_coe_finsupp** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n] {M : Type u_4}   [inst_3 : AddCommMonoid M] [inst_4 
: _root_.Module R M] [inst_5 : CoalgebraStruct R M] (x : n →₀ M),   CoalgebraStr
uct.comul ⇑x = (TensorProduct.map Finsupp.lcoeFun Finsupp.lcoeFun) (CoalgebraStr
uct.comul x)
参数：x : n →₀ M；TensorProduct.map Finsupp.lcoeFun Finsupp.lcoeFun；CoalgebraStruct.
comul x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.comul_comp_finsuppLcoeFun`：comul_comp_finsuppLcoeFun : comul (R
-/
@[simp] theorem comul_coe_finsupp (x : n →₀ M) :
    comul (R := R) ⇑x = map lcoeFun lcoeFun (comul x) :=
  congr($comul_comp_finsuppLcoeFun x)

end coalgebraStruct

variable [Π i, Coalgebra R (A i)]

/-- The `R`-module whose elements are functions `Π i, A i` for finite `n` has a coalgebra structure.
The coproduct `Δ` is given by `Δ(fᵢ a) = fᵢ a₁ ⊗ fᵢ a₂` where `Δ(a) = a₁ ⊗ a₂` and
the counit `ε` by `ε(fᵢ a) = ε(a)`, where `fᵢ a` is the function sending `i` to `a` and all
other elements of `ι` to zero. -/
/-
**Pi.instCoalgebra** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instCoalgebra : Coalgebra R (Π i, A i) where rTensor_counit_comp_comul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-module whose elements are functions `Π i, A i` for finite `n` has a coal
gebra structure.
The coproduct `Δ` is given by `Δ(fᵢ a) = fᵢ a₁ ⊗ fᵢ a₂` where `Δ(a) = a₁ ⊗ a₂` a
nd
the counit `ε` by `ε(fᵢ a) = ε(a)`, where `fᵢ a` is the function sending `i` to 
`a` and all
other elements of `ι` to zero.
-/
instance instCoalgebra : Coalgebra R (Π i, A i) where
  rTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc, comul_comp_single, ← comp_assoc, rTensor_comp_map, counit_comp_single,
      ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc, comul_comp_single, ← comp_assoc, lTensor_comp_map, counit_comp_single,
      ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
  coassoc := by
    ext : 1
    simp_rw [comp_assoc, comul_comp_single, ← comp_assoc, lTensor_comp_map, comul_comp_single,
      comp_assoc, ← comp_assoc comul, rTensor_comp_map, comul_comp_single, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc comul, ← comp_assoc,
      map_map_comp_assoc_eq]
/-
**Pi.instIsCocomm** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instIsCocomm [forall i, IsCocomm R (A i)] : IsCocomm R (Π i, A i) where co
mm_comp_comul
参数：A i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.comul_single`：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R]
 [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (i
 : n)…
· 使用定理 `Coalgebra.comm_comul`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R
] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3 : Coalgebra 
R A] [Coal…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instIsCocomm [∀ i, IsCocomm R (A i)] : IsCocomm R (Π i, A i) where
  comm_comp_comul := by ext; simp [← map_comm]

end Pi

namespace Equiv
variable {R A B : Type*} [CommSemiring R]

variable (R) in
/-- Transfer `CoalgebraStruct` across an `Equiv`. -/
/-
**Equiv.coalgebraStruct** 是 Mathlib 中的一个缩写定义，位于命名空间 `Equiv`。
形式化陈述：coalgebraStruct [AddCommMonoid B] [Module R B] [CoalgebraStruct R B] (e : 
A ≃ B) : letI
参数：e : A ≃ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `CoalgebraStruct` across an `Equiv`.
-/
abbrev coalgebraStruct [AddCommMonoid B] [Module R B] [CoalgebraStruct R B] (e : A ≃ B) :
    letI := e.addCommMonoid
    letI := e.module R
    CoalgebraStruct R A :=
  letI := e.addCommMonoid
  letI := e.module R
  { comul :=
      TensorProduct.map (e.linearEquiv R).symm.toLinearMap (e.linearEquiv R).symm.toLinearMap ∘ₗ
        comul ∘ₗ (e.linearEquiv R).toLinearMap
    counit := counit ∘ₗ (e.linearEquiv R).toLinearMap }

variable (R) in
/-- Transfer `Coalgebra` across an `Equiv`. -/
/-
**Equiv.coalgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 `Equiv`。
形式化陈述：coalgebra [AddCommMonoid B] [Module R B] [Coalgebra R B] (e : A ≃ B) : let
I
参数：e : A ≃ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `Coalgebra` across an `Equiv`.
-/
abbrev coalgebra [AddCommMonoid B] [Module R B] [Coalgebra R B] (e : A ≃ B) :
    letI := e.addCommMonoid
    letI := e.module R
    Coalgebra R A :=
  letI := e.addCommMonoid
  letI := e.module R
  { __ := e.coalgebraStruct R
    rTensor_counit_comp_comul := by
      ext
      apply (TensorProduct.map_bijective (f := .id) Function.bijective_id
        (e.linearEquiv R).bijective).injective
      simpa +instances [coalgebraStruct, LinearMap.comp_assoc, TensorProduct.map_map,
        LinearMap.rTensor] using! Coalgebra.rTensor_counit_comul _
    lTensor_counit_comp_comul := by
      ext
      apply (TensorProduct.map_bijective (g := .id) (e.linearEquiv R).bijective
        Function.bijective_id).injective
      simpa +instances [coalgebraStruct, LinearMap.comp_assoc, TensorProduct.map_map,
        LinearMap.lTensor] using! Coalgebra.lTensor_counit_comul _
    coassoc := by
      ext
      apply (TensorProduct.map_bijective (e.linearEquiv R).bijective <|
        TensorProduct.map_bijective (e.linearEquiv R).bijective
        (e.linearEquiv R).bijective).injective
      simp +instances [coalgebraStruct, e.tensorProductAssoc_def R, TensorProduct.congr,
        ← LinearMap.comp_assoc, TensorProduct.map_map, ← TensorProduct.map_comp]
      simpa [LinearMap.comp_assoc, -coassoc_apply] using! coassoc_apply (R := R) (A := B) _ }

variable (R) in
/-- Transfer `Coalgebra.IsCocomm` across an `Equiv`. -/
/-
**Equiv.coalgebraIsCocomm** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：coalgebraIsCocomm [AddCommMonoid B] [Module R B] [Coalgebra R B] [IsCocomm
 R B] (e : A ≃ B) : letI
参数：e : A ≃ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Coalgebra.comm_comul`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R
] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3 : Coalgebra 
R A] [Coal…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Transfer `Coalgebra.IsCocomm` across an `Equiv`.
-/
lemma coalgebraIsCocomm [AddCommMonoid B] [Module R B] [Coalgebra R B] [IsCocomm R B] (e : A ≃ B) :
    letI := e.addCommMonoid
    letI := e.module R
    letI := e.coalgebra R
    IsCocomm R A :=
  letI := e.addCommMonoid
  letI := e.module R
  letI := e.coalgebra R
  { comm_comp_comul := by ext; simp [comul, ← TensorProduct.map_comm] }

end Equiv

