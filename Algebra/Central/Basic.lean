/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Jujian Zhang, Yunzhou Xie
-/
module

public import Mathlib.Algebra.Central.Defs

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Central Algebras

In this file, we prove some basic results about central algebras over a commutative ring.

## Main results

- `Algebra.IsCentral.center_eq_bot`: the center of a central algebra over `K` is equal to `K`.
- `Algebra.IsCentral.self`: a commutative ring is a central algebra over itself.
- `Algebra.IsCentral.baseField_essentially_unique`: Let `D/K/k` be a tower of scalars where
  `K` and `k` are fields. If `D` is a nontrivial central algebra over `k`, `K` is isomorphic to `k`.
-/

public section

universe u v

namespace Algebra.IsCentral

variable (K : Type u) [CommSemiring K] (D D' : Type v) [Semiring D] [Algebra K D]
  [h : IsCentral K D] [Semiring D'] [Algebra K D']

@[simp]
/-
**Algebra.IsCentral.center_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsCentral`。
形式化陈述：center_eq_bot : Subalgebra.center K D = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Algebra.IsCentral.out`：∀ {K : Type u} {inst : CommSemiring K} {D : Type 
v} {inst_1 : Semiring D} {inst_2 : Algebra K D}   [self : Algebra.IsCentral K D]
, Subalgebr…
-/
lemma center_eq_bot : Subalgebra.center K D = ⊥ := eq_bot_iff.2 IsCentral.out

variable {D} in
/-
**Algebra.IsCentral.mem_center_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsCentral`
。
形式化陈述：mem_center_iff {x : D} : x in Subalgebra.center K D ↔ exists (a : K), x = 
algebraMap K D a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.IsCentral.center_eq_bot`：center_eq_bot : Subalgebra.center K D =
 ⊥
· 使用定理 `Algebra.mem_bot`：mem_bot {x : A} : x in (⊥ : Subalgebra R A) ↔ x in Set.
range (algebraMap R A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_center_iff {x : D} : x ∈ Subalgebra.center K D ↔ ∃ (a : K), x = algebraMap K D a := by
  rw [center_eq_bot, Algebra.mem_bot]
  simp [eq_comm]
/-
**Algebra.IsCentral.self** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsCentral`。
形式化陈述：self : IsCentral K K where out x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.center_eq_top`：center_eq_top (A : Type*) [CommSemiring A] [Al
gebra R A] : center R A = ⊤
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
-/
instance self : IsCentral K K where
  out x := by simp [Algebra.mem_bot]
/-
**Algebra.IsCentral.baseField_essentially_unique** 是 Mathlib 中的一个引理，位于命名空间 `Alge
bra.IsCentral`。
形式化陈述：baseField_essentially_unique (k K D : Type*) [Field k] [Field K] [Ring D] 
[Nontrivial D] [Algebra k K] [Algebra K D] [Algebra k D] [IsScalarTower k K D] [
IsCentral k D] : Function.Bijective (algebraMap k K)
参数：k K D : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.IsCentral.center_eq_bot`：center_eq_bot : Subalgebra.center K D =
 ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma baseField_essentially_unique
    (k K D : Type*) [Field k] [Field K] [Ring D] [Nontrivial D]
    [Algebra k K] [Algebra K D] [Algebra k D] [IsScalarTower k K D]
    [IsCentral k D] :
    Function.Bijective (algebraMap k K) := by
  have : IsCentral K D :=
  { out := fun x ↦ show x ∈ Subalgebra.center k D → _ by
      simp only [center_eq_bot, mem_bot, Set.mem_range, forall_exists_index]
      rintro x rfl
      exact ⟨algebraMap k K x, by simp [algebraMap_eq_smul_one, smul_assoc]⟩ }
  refine ⟨FaithfulSMul.algebraMap_injective k K, fun x => ?_⟩
  have H : algebraMap K D x ∈ (Subalgebra.center K D : Set D) := Subalgebra.algebraMap_mem _ _
  rw [show (Subalgebra.center K D : Set D) = Subalgebra.center k D by rfl] at H
  simp only [center_eq_bot, coe_bot, Set.mem_range] at H
  obtain ⟨x', H⟩ := H
  exact ⟨x', (algebraMap K D).injective <| by simp [← H, algebraMap_eq_smul_one]⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.IsCentral.of_algEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsCentral`。
形式化陈述：of_algEquiv (e : D ≃ₐ[K] D') : IsCentral K D' where out x hx
参数：e : D ≃ₐ[K] D'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsCentral.out`：∀ {K : Type u} {inst : CommSemiring K} {D : Type 
v} {inst_1 : Semiring D} {inst_2 : Algebra K D}   [self : Algebra.IsCentral K D]
, Subalgebr…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulEquivClass.apply_mem_center_iff`：∀ {M : Type u_3} {N : Type u_1} {F :
 Type u_2} [inst : EquivLike F M N] [inst_1 : Mul M] [inst_2 : Mul N]   [MulEqui
vClass F M N] (e : F) {x…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
-/
lemma of_algEquiv (e : D ≃ₐ[K] D') : IsCentral K D' where
  out x hx :=
    have ⟨k, hk⟩ := h.1 ((MulEquivClass.apply_mem_center_iff e.symm).mpr hx)
    ⟨k, by simpa [ofId] using congr(e $hk)⟩

open MulOpposite in
/-- Opposite algebra of a central algebra is central. This instance combined with the coming
  `IsSimpleRing` instance for the opposite of central simple algebra will be an
  inverse for an element in `BrauerGroup`, find out more about this in
  `Mathlib/Algebra/BrauerGroup/Defs.lean`. -/
/-
**Algebra.IsCentral.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsCentral`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Opposite algebra of a central algebra is central. This instance combined with th
e coming
  `IsSimpleRing` instance for the opposite of central simple algebra will be an
  inverse for an element in `BrauerGroup`, find out more about this in
  `Mathlib/Algebra/BrauerGroup/Defs.lean`.
-/
instance : IsCentral K Dᵐᵒᵖ where
  out z hz :=
    have ⟨k, hk⟩ := h.1 (MulOpposite.unop_mem_center_iff.mpr hz)
    ⟨k, by simpa using congr(op $hk)⟩

end Algebra.IsCentral

