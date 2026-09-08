/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Properties of centers and centralizers

This file contains theorems about the center and centralizer of a subalgebra.

## Main results

Let `R` be a commutative ring and `A` and `B` two `R`-algebras.
- `Subalgebra.centralizer_sup`: if `S` and `T` are subalgebras of `A`, then the centralizer of
  `S ⊔ T` is the intersection of the centralizer of `S` and the centralizer of `T`.
- `Subalgebra.centralizer_range_includeLeft_eq_center_tensorProduct`: if `B` is free as a module,
  then the centralizer of `A ⊗ 1` in `A ⊗ B` is `C(A) ⊗ B` where `C(A)` is the center of `A`.
- `Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct`: if `A` is free as a module,
  then the centralizer of `1 ⊗ B` in `A ⊗ B` is `A ⊗ C(B)` where `C(B)` is the center of `B`.
-/

public section

namespace Subalgebra

open Algebra.TensorProduct

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable {A : Type*} [Semiring A] [Algebra R A]

/-
**Subalgebra.le_centralizer_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：le_centralizer_iff (S T : Subalgebra R A) : S <= centralizer R T ↔ T <= ce
ntralizer R S
参数：S T : Subalgebra R A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma le_centralizer_iff (S T : Subalgebra R A) : S ≤ centralizer R T ↔ T ≤ centralizer R S :=
  ⟨fun h t ht _ hs ↦ (h hs t ht).symm, fun h s hs _ ht ↦ (h ht s hs).symm⟩
/-
**Subalgebra.centralizer_coe_sup** 是 Mathlib 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：centralizer_coe_sup (S T : Subalgebra R A) : centralizer R ((S ⊔ T : Subal
gebra R A) : Set A) = centralizer R S ⊓ centralizer R T
参数：S T : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Subalgebra.le_centralizer_iff`：le_centralizer_iff (S T : Subalgebra R A)
 : S <= centralizer R T ↔ T <= centralizer R S
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma centralizer_coe_sup (S T : Subalgebra R A) :
    centralizer R ((S ⊔ T : Subalgebra R A) : Set A) = centralizer R S ⊓ centralizer R T :=
  eq_of_forall_le_iff fun K ↦ by
    simp_rw [le_centralizer_iff, sup_le_iff, le_inf_iff, K.le_centralizer_iff]
/-
**Subalgebra.centralizer_coe_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：centralizer_coe_iSup {ι : Sort*} (S : ι -> Subalgebra R A) : centralizer R
 ((⨆ i, S i : Subalgebra R A) : Set A) = ⨅ i, centralizer R (S i)
参数：S : ι -> Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Subalgebra.le_centralizer_iff`：le_centralizer_iff (S T : Subalgebra R A)
 : S <= centralizer R T ↔ T <= centralizer R S
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma centralizer_coe_iSup {ι : Sort*} (S : ι → Subalgebra R A) :
    centralizer R ((⨆ i, S i : Subalgebra R A) : Set A) = ⨅ i, centralizer R (S i) :=
  eq_of_forall_le_iff fun K ↦ by
    simp_rw [le_centralizer_iff, iSup_le_iff, le_iInf_iff, K.le_centralizer_iff]

end CommSemiring

section Free

variable (R : Type*) [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable (B : Type*) [Semiring B] [Algebra R B]

open Finsupp TensorProduct

/--
Let `R` be a commutative ring and `A, B` be `R`-algebras where `B` is free as `R`-module.
For any subset `S ⊆ A`, the centralizer of `S ⊗ 1 ⊆ A ⊗ B` is `C_A(S) ⊗ B` where `C_A(S)` is the
centralizer of `S` in `A`.
-/
/-
**Subalgebra.centralizer_coe_image_includeLeft_eq_center_tensorProduct** 是 Mathl
ib 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：centralizer_coe_image_includeLeft_eq_center_tensorProduct (S : Set A) [Mod
ule.Free R B] : Subalgebra.centralizer R (Algebra.TensorProduct.includeLeft (S
参数：S : Set A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
· 使用引理 `TensorProduct.eq_repr_basis_right`：TensorProduct.eq_repr_basis_right : e
xists b : κ ->₀ M, b.sum (fun i m => m otimesₜ 𝒞 i) = x
· 使用定理 `Subalgebra.sum_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {ι : Type w}
 {t : Fi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.mem_centralizer_iff`：mem_centralizer_iff {s : Set A} {z : A} 
: z in centralizer R s ↔ forall g in s, g * z = z * g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `TensorProduct.sum_tmul_basis_right_injective`：TensorProduct.sum_tmul_bas
is_right_injective : Function.Injective (Finsupp.lsum R fun i => (TensorProduct.
mk R M N).flip (𝒞 i))
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …
· 使用定理 `Finsupp.support_smul`：support_smul [Zero M] [SMulZeroClass R M] {b : R} 
{g : α ->₀ M} : (b • g).support subseteq g.support
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
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
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.support_mapRange`：support_mapRange {f : M -> N} {hf : f 0 = 0} {
g : α ->₀ M} : (mapRange f hf g).support subseteq g.support
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
Let `R` be a commutative ring and `A, B` be `R`-algebras where `B` is free as `R
`-module.
For any subset `S ⊆ A`, the centralizer of `S ⊗ 1 ⊆ A ⊗ B` is `C_A(S) ⊗ B` where
 `C_A(S)` is the
centralizer of `S` in `A`.
-/
lemma centralizer_coe_image_includeLeft_eq_center_tensorProduct
    (S : Set A) [Module.Free R B] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeLeft (S := R) '' S) =
    (Algebra.TensorProduct.map (Subalgebra.centralizer R (S : Set A)).val
      (AlgHom.id R B)).range := by
  ext w
  constructor
  · intro hw
    rw [mem_centralizer_iff] at hw
    let ℬ := Module.Free.chooseBasis R B
    obtain ⟨b, rfl⟩ := TensorProduct.eq_repr_basis_right ℬ w
    refine Subalgebra.sum_mem _ fun j hj => ⟨⟨b j, ?_⟩ ⊗ₜ[R] ℬ j, by simp⟩
    rw [Subalgebra.mem_centralizer_iff]
    intro x hx
    suffices x • b = b.mapRange (· * x) (by simp) from Finsupp.ext_iff.1 this j
    specialize hw (x ⊗ₜ[R] 1) ⟨x, hx, rfl⟩
    simp only [Finsupp.sum, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Finset.sum_mul, mul_one] at hw
    refine TensorProduct.sum_tmul_basis_right_injective ℬ ?_
    simp only [Finsupp.coe_lsum]
    rw [sum_of_support_subset (s := b.support) (hs := Finsupp.support_smul) (h := by simp),
      sum_of_support_subset (s := b.support) (hs := support_mapRange) (h := by simp)]
    simpa only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, LinearMap.flip_apply,
      TensorProduct.mk_apply, Finsupp.mapRange_apply] using hw
  · rintro ⟨w, rfl⟩
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      simp [Subalgebra.mem_centralizer_iff _ |>.1 b.2 x hx]
    | add y z hy hz => rw [map_add, mul_add, hy, hz, add_mul]

/--
Let `R` be a commutative ring and `A, B` be `R`-algebras where `B` is free as `R`-module.
For any subset `S ⊆ B`, the centralizer of `1 ⊗ S ⊆ A ⊗ B` is `A ⊗ C_B(S)` where `C_B(S)` is the
centralizer of `S` in `B`.
-/
/-
**Subalgebra.centralizer_coe_image_includeRight_eq_center_tensorProduct** 是 Math
lib 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：centralizer_coe_image_includeRight_eq_center_tensorProduct (S : Set B) [Mo
dule.Free R A] : Subalgebra.centralizer R (Algebra.TensorProduct.includeRight ''
 S) = (Algebra.TensorProduct.map (AlgHom.id R A) (Subalgebra.centralizer R (S : 
Set B)).val).range
参数：S : Set B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
· 使用引理 `Subalgebra.centralizer_coe_image_includeLeft_eq_center_tensorProduct`：ce
ntralizer_coe_image_includeLeft_eq_center_tensorProduct (S : Set A) [Module.Free
 R B] : Subalgebra.centralizer R (Algebra.TensorProduct.in…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Algebra.TensorProduct.comm_comp_map_apply`：comm_comp_map_apply (f : A ->
ₐ[R] C) (g : B ->ₐ[R] D) (x) : TensorProduct.comm R C D (Algebra.TensorProduct.m
ap f g x) = (Algebra.TensorProd…
· 使用定理 `Algebra.TensorProduct.comm_symm`：comm_symm : (TensorProduct.comm R A B).
symm = TensorProduct.comm R B A

--- 原说明 ---
Let `R` be a commutative ring and `A, B` be `R`-algebras where `B` is free as `R
`-module.
For any subset `S ⊆ B`, the centralizer of `1 ⊗ S ⊆ A ⊗ B` is `A ⊗ C_B(S)` where
 `C_B(S)` is the
centralizer of `S` in `B`.
-/
lemma centralizer_coe_image_includeRight_eq_center_tensorProduct
    (S : Set B) [Module.Free R A] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeRight '' S) =
    (Algebra.TensorProduct.map (AlgHom.id R A)
      (Subalgebra.centralizer R (S : Set B)).val).range := by
  have eq1 := centralizer_coe_image_includeLeft_eq_center_tensorProduct R B A S
  apply_fun Subalgebra.comap (Algebra.TensorProduct.comm R A B).toAlgHom at eq1
  convert! eq1
  · ext x
    simpa [mem_centralizer_iff] using
      ⟨fun h b hb ↦ (Algebra.TensorProduct.comm R A B).symm.injective <| by aesop, fun h b hb ↦
        (Algebra.TensorProduct.comm R A B).injective <| by aesop⟩
  · ext x
    simp only [AlgHom.mem_range, mem_comap, AlgEquiv.coe_toAlgHom]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(Algebra.TensorProduct.comm R _ _) x,
        by rw [Algebra.TensorProduct.comm_comp_map_apply]⟩
    · rintro ⟨y, hy⟩
      refine ⟨(Algebra.TensorProduct.comm R _ _) y, (Algebra.TensorProduct.comm R A B).injective ?_⟩
      rw [← hy, comm_comp_map_apply, ← Algebra.TensorProduct.comm_symm, AlgEquiv.symm_apply_apply]

/--
Let `R` be a commutative ring and `A, B` be `R`-algebras where `B` is free as `R`-module.
For any subalgebra `S` of `A`, the centralizer of `S ⊗ 1 ⊆ A ⊗ B` is `C_A(S) ⊗ B` where `C_A(S)` is
the centralizer of `S` in `A`.
-/
/-
**Subalgebra.centralizer_coe_map_includeLeft_eq_center_tensorProduct** 是 Mathlib
 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：centralizer_coe_map_includeLeft_eq_center_tensorProduct (S : Subalgebra R 
A) [Module.Free R B] : Subalgebra.centralizer R (S.map (Algebra.TensorProduct.in
cludeLeft (R
参数：S : Subalgebra R A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subalgebra.centralizer_coe_image_includeLeft_eq_center_tensorProduct`：ce
ntralizer_coe_image_includeLeft_eq_center_tensorProduct (S : Set A) [Module.Free
 R B] : Subalgebra.centralizer R (Algebra.TensorProduct.in…

--- 原说明 ---
Let `R` be a commutative ring and `A, B` be `R`-algebras where `B` is free as `R
`-module.
For any subalgebra `S` of `A`, the centralizer of `S ⊗ 1 ⊆ A ⊗ B` is `C_A(S) ⊗ B
` where `C_A(S)` is
the centralizer of `S` in `A`.
-/
lemma centralizer_coe_map_includeLeft_eq_center_tensorProduct
    (S : Subalgebra R A) [Module.Free R B] :
    Subalgebra.centralizer R
      (S.map (Algebra.TensorProduct.includeLeft (R := R) (B := B))) =
    (Algebra.TensorProduct.map (Subalgebra.centralizer R (S : Set A)).val
      (AlgHom.id R B)).range :=
  centralizer_coe_image_includeLeft_eq_center_tensorProduct R A B S

/--
Let `R` be a commutative ring and `A, B` be `R`-algebras where `A` is free as `R`-module.
For any subalgebra `S` of `B`, the centralizer of `1 ⊗ S ⊆ A ⊗ B` is `A ⊗ C_B(S)` where `C_B(S)` is
the centralizer of `S` in `B`.
-/
/-
**Subalgebra.centralizer_coe_map_includeRight_eq_center_tensorProduct** 是 Mathli
b 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：centralizer_coe_map_includeRight_eq_center_tensorProduct (S : Subalgebra R
 B) [Module.Free R A] : Subalgebra.centralizer R (S.map (Algebra.TensorProduct.i
ncludeRight (R
参数：S : Subalgebra R B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subalgebra.centralizer_coe_image_includeRight_eq_center_tensorProduct`：c
entralizer_coe_image_includeRight_eq_center_tensorProduct (S : Set B) [Module.Fr
ee R A] : Subalgebra.centralizer R (Algebra.TensorProduct.i…

--- 原说明 ---
Let `R` be a commutative ring and `A, B` be `R`-algebras where `A` is free as `R
`-module.
For any subalgebra `S` of `B`, the centralizer of `1 ⊗ S ⊆ A ⊗ B` is `A ⊗ C_B(S)
` where `C_B(S)` is
the centralizer of `S` in `B`.
-/
lemma centralizer_coe_map_includeRight_eq_center_tensorProduct
    (S : Subalgebra R B) [Module.Free R A] :
    Subalgebra.centralizer R
      (S.map (Algebra.TensorProduct.includeRight (R := R) (A := A))) =
    (Algebra.TensorProduct.map (AlgHom.id R A)
      (Subalgebra.centralizer R (S : Set B)).val).range :=
  centralizer_coe_image_includeRight_eq_center_tensorProduct R A B S

/--
Let `R` be a commutative ring and `A, B` be `R`-algebras where `B` is free as `R`-module.
Then the centralizer of `A ⊗ 1 ⊆ A ⊗ B` is `C(A) ⊗ B` where `C(A)` is the center of `A`.
-/
/-
**Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct** 是 Mathl
ib 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：centralizer_coe_range_includeLeft_eq_center_tensorProduct [Module.Free R B
] : Subalgebra.centralizer R (Algebra.TensorProduct.includeLeft : A ->ₐ[R] A oti
mes[R] B).range = (Algebra.TensorProduct.map (Subalgebra.center R A).val (AlgHom
.id R B)).range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.centralizer_univ`：centralizer_univ : centralizer R Set.univ =
 center R A
· 使用定理 `Algebra.coe_top`：coe_top : (↑(⊤ : Subalgebra R A) : Set A) = Set.univ
· 使用引理 `Subalgebra.centralizer_coe_map_includeLeft_eq_center_tensorProduct`：cent
ralizer_coe_map_includeLeft_eq_center_tensorProduct (S : Subalgebra R A) [Module
.Free R B] : Subalgebra.centralizer R (S.map (Algebra.Te…
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Let `R` be a commutative ring and `A, B` be `R`-algebras where `B` is free as `R
`-module.
Then the centralizer of `A ⊗ 1 ⊆ A ⊗ B` is `C(A) ⊗ B` where `C(A)` is the center
 of `A`.
-/
lemma centralizer_coe_range_includeLeft_eq_center_tensorProduct [Module.Free R B] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).range =
    (Algebra.TensorProduct.map (Subalgebra.center R A).val (AlgHom.id R B)).range := by
  rw [← centralizer_univ, ← Algebra.coe_top (R := R) (A := A),
    ← centralizer_coe_map_includeLeft_eq_center_tensorProduct R A B ⊤]
  ext
  simp [includeLeft, includeLeftRingHom]

/--
Let `R` be a commutative ring and `A, B` be `R`-algebras where `A` is free as `R`-module.
Then the centralizer of `1 ⊗ B ⊆ A ⊗ B` is `A ⊗ C(B)` where `C(B)` is the center of `B`.
-/
/-
**Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct** 是 Mathlib 
中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：centralizer_range_includeRight_eq_center_tensorProduct [Module.Free R A] :
 Subalgebra.centralizer R (Algebra.TensorProduct.includeRight : B ->ₐ[R] A otime
s[R] B).range = (Algebra.TensorProduct.map (AlgHom.id R A) (center R B).val).ran
ge
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.centralizer_univ`：centralizer_univ : centralizer R Set.univ =
 center R A
· 使用定理 `Algebra.coe_top`：coe_top : (↑(⊤ : Subalgebra R A) : Set A) = Set.univ
· 使用引理 `Subalgebra.centralizer_coe_map_includeRight_eq_center_tensorProduct`：cen
tralizer_coe_map_includeRight_eq_center_tensorProduct (S : Subalgebra R B) [Modu
le.Free R A] : Subalgebra.centralizer R (S.map (Algebra.T…
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `TensorProduct.AlgebraTensorModule.mk_apply`：∀ (R : Type uR) [inst : Comm
Semiring R] (A : Type u_1) (M : Type u_2) (N : Type u_3) [inst_1 : Semiring A]  
 [inst_2 : AddCommMonoid M] [ins…
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `RingHom.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocS
emiring α] [inst_1 : NonAssocSemiring β]   (toMonoidHom toMonoidHom_1 : α →* β) 
(e_toMonoid…
· 使用定理 `AlgHom.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R
 A] [inst_…
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Let `R` be a commutative ring and `A, B` be `R`-algebras where `A` is free as `R
`-module.
Then the centralizer of `1 ⊗ B ⊆ A ⊗ B` is `A ⊗ C(B)` where `C(B)` is the center
 of `B`.
-/
lemma centralizer_range_includeRight_eq_center_tensorProduct [Module.Free R A] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).range =
    (Algebra.TensorProduct.map (AlgHom.id R A) (center R B).val).range := by
  rw [← centralizer_univ, ← Algebra.coe_top (R := R) (A := B),
    ← centralizer_coe_map_includeRight_eq_center_tensorProduct R A B ⊤]
  ext
  simp [includeRight]
/-
**Subalgebra.centralizer_tensorProduct_eq_center_tensorProduct_left** 是 Mathlib 
中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：centralizer_tensorProduct_eq_center_tensorProduct_left [Module.Free R B] :
 Subalgebra.centralizer R (Algebra.TensorProduct.map (AlgHom.id R A) (Algebra.of
Id R B)).range = (Algebra.TensorProduct.map (Subalgebra.center R A).val (AlgHom.
id R B)).range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct`：ce
ntralizer_coe_range_includeLeft_eq_center_tensorProduct [Module.Free R B] : Suba
lgebra.centralizer R (Algebra.TensorProduct.includeLeft : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.TensorProduct.map_range`：map_range (f : A ->ₐ[R] C) (g : B ->ₐ[R
] D) : (map f g).range = (includeLeft.comp f).range ⊔ (includeRight.comp g).rang
e
· 使用定理 `Algebra.comp_ofId`：comp_ofId (φ : A ->ₐ[R] B) : φ.comp (Algebra.ofId R A
) = Algebra.ofId R B
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma centralizer_tensorProduct_eq_center_tensorProduct_left [Module.Free R B] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.map (AlgHom.id R A) (Algebra.ofId R B)).range =
    (Algebra.TensorProduct.map (Subalgebra.center R A).val (AlgHom.id R B)).range := by
  rw [← centralizer_coe_range_includeLeft_eq_center_tensorProduct]
  simp [Algebra.TensorProduct.map_range]
/-
**Subalgebra.centralizer_tensorProduct_eq_center_tensorProduct_right** 是 Mathlib
 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：centralizer_tensorProduct_eq_center_tensorProduct_right [Module.Free R A] 
: Subalgebra.centralizer R (Algebra.TensorProduct.map (Algebra.ofId R A) (AlgHom
.id R B)).range = (Algebra.TensorProduct.map (AlgHom.id R A) (center R B).val).r
ange
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct`：centr
alizer_range_includeRight_eq_center_tensorProduct [Module.Free R A] : Subalgebra
.centralizer R (Algebra.TensorProduct.includeRight : B …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.TensorProduct.map_range`：map_range (f : A ->ₐ[R] C) (g : B ->ₐ[R
] D) : (map f g).range = (includeLeft.comp f).range ⊔ (includeRight.comp g).rang
e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.comp_ofId`：comp_ofId (φ : A ->ₐ[R] B) : φ.comp (Algebra.ofId R A
) = Algebra.ofId R B
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma centralizer_tensorProduct_eq_center_tensorProduct_right [Module.Free R A] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.map (Algebra.ofId R A) (AlgHom.id R B)).range =
    (Algebra.TensorProduct.map (AlgHom.id R A) (center R B).val).range := by
  rw [← centralizer_range_includeRight_eq_center_tensorProduct]
  simp [Algebra.TensorProduct.map_range]

end Free

end Subalgebra

