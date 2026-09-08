/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Integral closure of a subring.

Let `A` be an `R`-algebra. We prove that integral elements form a sub-`R`-algebra of `A`.

## Main definitions

Let `R` be a `CommRing` and let `A` be an R-algebra.

* `integralClosure R A` : the integral closure of `R` in an `R`-algebra `A`.
-/

@[expose] public section


open Polynomial Submodule

section

variable {R A B S : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S]
variable [Algebra R A] [Algebra R B] (f : R →+* S)

/-
**Subalgebra.isIntegral_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.isIntegral_iff (S : Subalgebra R B) : Algebra.IsIntegral R S ↔ 
forall x in S, IsIntegral R x
参数：S : Subalgebra R B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Algebra.isIntegral_def`：Algebra.isIntegral_def : Algebra.IsIntegral R A 
↔ forall x : A, IsIntegral R x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem Subalgebra.isIntegral_iff (S : Subalgebra R B) :
    Algebra.IsIntegral R S ↔ ∀ x ∈ S, IsIntegral R x :=
  Algebra.isIntegral_def.trans <| .trans
    (forall_congr' fun _ ↦ (isIntegral_algHom_iff S.val Subtype.val_injective).symm) Subtype.forall

section

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-
**Algebra.IsIntegral.of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.of_injective (f : A ->ₐ[R] B) (hf : Function.Injective 
f) [Algebra.IsIntegral R B] : Algebra.IsIntegral R A
参数：f : A ->ₐ[R] B；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
-/
theorem Algebra.IsIntegral.of_injective (f : A →ₐ[R] B) (hf : Function.Injective f)
    [Algebra.IsIntegral R B] : Algebra.IsIntegral R A :=
  ⟨fun _ ↦ (isIntegral_algHom_iff f hf).mp (isIntegral _)⟩

/-- Homomorphic image of an integral algebra is an integral algebra. -/
/-
**Algebra.IsIntegral.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.of_surjective [Algebra.IsIntegral R A] (f : A ->ₐ[R] B)
 (hf : Function.Surjective f) : Algebra.IsIntegral R B
参数：f : A ->ₐ[R] B；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Algebra.isIntegral_def`：Algebra.isIntegral_def : Algebra.IsIntegral R A 
↔ forall x : A, IsIntegral R x
· 使用定理 `IsIntegral.map`：IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebr
a R B] [Algebra A B] [Algebra R C] [IsScalarTower R A B] [Algebra A C] [IsScalar
Towe…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
Homomorphic image of an integral algebra is an integral algebra.
-/
theorem Algebra.IsIntegral.of_surjective [Algebra.IsIntegral R A]
    (f : A →ₐ[R] B) (hf : Function.Surjective f) : Algebra.IsIntegral R B :=
  isIntegral_def.mpr fun b ↦ let ⟨a, ha⟩ := hf b; ha ▸ (isIntegral_def.mp ‹_› a).map f
/-
**AlgEquiv.isIntegral_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.isIntegral_iff (e : A ≃ₐ[R] B) : Algebra.IsIntegral R A ↔ Algebra
.IsIntegral R B
参数：e : A ≃ₐ[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsIntegral.of_injective`：Algebra.IsIntegral.of_injective (f : A 
->ₐ[R] B) (hf : Function.Injective f) [Algebra.IsIntegral R B] : Algebra.IsInteg
ral R A
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
theorem AlgEquiv.isIntegral_iff (e : A ≃ₐ[R] B) : Algebra.IsIntegral R A ↔ Algebra.IsIntegral R B :=
  ⟨fun h ↦ h.of_injective e.symm e.symm.injective, fun h ↦ h.of_injective e e.injective⟩

end

/-
**Module.End.isIntegral** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.End.isIntegral {M : Type*} [AddCommGroup M] [Module R M] [Module.Fi
nite R M] : Algebra.IsIntegral R (Module.End R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.exists_monic_and_aeval_eq_zero`：LinearMap.exists_monic_and_aev
al_eq_zero [Module.Finite R M] (f : Module.End R M) : exists p : R[X], p.Monic ∧
 Polynomial.aeval f p = 0
-/
instance Module.End.isIntegral {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Algebra.IsIntegral R (Module.End R M) :=
  ⟨LinearMap.exists_monic_and_aeval_eq_zero R⟩

variable (R) in
@[nontriviality]
/-
**IsIntegral.of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.of_finite [Module.Finite R B] (x : B) : IsIntegral R x
参数：x : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x
· 使用定理 `Algebra.lmul_injective`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemi
ring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   Function.Injective ⇑(Alg
ebra.lmul R …
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
-/
theorem IsIntegral.of_finite [Module.Finite R B] (x : B) : IsIntegral R x :=
  (isIntegral_algHom_iff (Algebra.lmul R B) Algebra.lmul_injective).mp
    (Algebra.IsIntegral.isIntegral _)
/-
**isIntegral_of_noetherian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_of_noetherian (_ : IsNoetherian R B) (x : B) : IsIntegral R x
参数：_ : IsNoetherian R B；x : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.of_finite`：IsIntegral.of_finite [Module.Finite R B] (x : B) :
 IsIntegral R x
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
-/
theorem isIntegral_of_noetherian (_ : IsNoetherian R B) (x : B) : IsIntegral R x :=
  .of_finite R x

variable (R B) in
/-
**Algebra.IsIntegral.of_finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.of_finite [Module.Finite R B] : Algebra.IsIntegral R B
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.of_finite`：IsIntegral.of_finite [Module.Finite R B] (x : B) :
 IsIntegral R x
-/
instance Algebra.IsIntegral.of_finite [Module.Finite R B] : Algebra.IsIntegral R B :=
  ⟨.of_finite R⟩
/-
**Algebra.isIntegral_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.isIntegral_of_surjective (H : Function.Surjective (algebraMap R B)
) : Algebra.IsIntegral R B
参数：H : Function.Surjective (algebraMap R B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsIntegral.of_surjective`：Algebra.IsIntegral.of_surjective [Alge
bra.IsIntegral R A] (f : A ->ₐ[R] B) (hf : Function.Surjective f) : Algebra.IsIn
tegral R B
-/
lemma Algebra.isIntegral_of_surjective (H : Function.Surjective (algebraMap R B)) :
    Algebra.IsIntegral R B :=
  .of_surjective (Algebra.ofId R B) H

/-- If `S` is a sub-`R`-algebra of `A` and `S` is finitely-generated as an `R`-module,
  then all elements of `S` are integral over `R`. -/
/-
**IsIntegral.of_mem_of_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.of_mem_of_fg (S : Subalgebra R B) (HS : S.toSubmodule.FG) (x : 
B) (hx : x in S) : IsIntegral R x
参数：S : Subalgebra R B；HS : S.toSubmodule.FG；x : B；hx : x in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `IsIntegral.of_finite`：IsIntegral.of_finite [Module.Finite R B] (x : B) :
 IsIntegral R x

--- 原说明 ---
If `S` is a sub-`R`-algebra of `A` and `S` is finitely-generated as an `R`-modul
e,
  then all elements of `S` are integral over `R`.
-/
theorem IsIntegral.of_mem_of_fg (S : Subalgebra R B)
    (HS : S.toSubmodule.FG) (x : B) (hx : x ∈ S) : IsIntegral R x :=
  have : Module.Finite R S := .of_fg HS
  (isIntegral_algHom_iff S.val Subtype.val_injective).mpr (.of_finite R (⟨x, hx⟩ : S))
/-
**isIntegral_of_submodule_noetherian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_of_submodule_noetherian (S : Subalgebra R B) (H : IsNoetherian 
R (Subalgebra.toSubmodule S)) (x : B) (hx : x in S) : IsIntegral R x
参数：S : Subalgebra R B；H : IsNoetherian R (Subalgebra.toSubmodule S)；x : B；hx : x
 in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.of_mem_of_fg`：IsIntegral.of_mem_of_fg (S : Subalgebra R B) (H
S : S.toSubmodule.FG) (x : B) (hx : x in S) : IsIntegral R x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.fg_top`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (N : Submodule R M), ⊤.F
G ↔ N.…
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
-/
theorem isIntegral_of_submodule_noetherian (S : Subalgebra R B)
    (H : IsNoetherian R (Subalgebra.toSubmodule S)) (x : B) (hx : x ∈ S) : IsIntegral R x :=
  .of_mem_of_fg _ ((Submodule.fg_top _).mp <| H.noetherian _) _ hx

/-- Suppose `A` is an `R`-algebra, `M` is an `A`-module such that `a • m ≠ 0` for all non-zero `a`
and `m`. If `x : A` fixes a nontrivial f.g. `R`-submodule `N` of `M`, then `x` is `R`-integral. -/
/-
**isIntegral_of_smul_mem_submodule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_of_smul_mem_submodule [IsDomain A] {M : Type*} [AddCommGroup M]
 [Module R M] [Module A M] [IsScalarTower R A M] [Module.IsTorsionFree A M] (N :
 Submodule R M) (hN : N != ⊥) (hN' : N.FG) (x : A) (hx : forall n in N, x • n in
 N) : IsIntegral R x
参数：N : Submodule R M；hN : N != ⊥；hN' : N.FG；x : A；hx : forall n in N, x • n in N
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `smul_eq_zero_iff_left`：smul_eq_zero_iff_left (hm : m != 0) : r • m = 0 ↔
 r = 0
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Suppose `A` is an `R`-algebra, `M` is an `A`-module such that `a • m ≠ 0` for al
l non-zero `a`
and `m`. If `x : A` fixes a nontrivial f.g. `R`-submodule `N` of `M`, then `x` i
s `R`-integral.
-/
theorem isIntegral_of_smul_mem_submodule [IsDomain A] {M : Type*} [AddCommGroup M] [Module R M]
    [Module A M] [IsScalarTower R A M] [Module.IsTorsionFree A M] (N : Submodule R M) (hN : N ≠ ⊥)
    (hN' : N.FG) (x : A) (hx : ∀ n ∈ N, x • n ∈ N) : IsIntegral R x := by
  let A' : Subalgebra R A :=
    { carrier := { x | ∀ n ∈ N, x • n ∈ N }
      mul_mem' := fun {a b} ha hb n hn => smul_smul a b n ▸ ha _ (hb _ hn)
      one_mem' := fun n hn => (one_smul A n).symm ▸ hn
      add_mem' := fun {a b} ha hb n hn => (add_smul a b n).symm ▸ N.add_mem (ha _ hn) (hb _ hn)
      zero_mem' := fun n _hn => (zero_smul A n).symm ▸ N.zero_mem
      algebraMap_mem' := fun r n hn => (algebraMap_smul A r n).symm ▸ N.smul_mem r hn }
  let f : A' →ₐ[R] Module.End R N :=
    AlgHom.ofLinearMap
      { toFun := fun x => (DistribSMul.toLinearMap R M x).restrict x.prop
        map_add' := by intro x y; ext; exact add_smul _ _ _
        map_smul' := by intro r s; ext; apply smul_assoc }
      (by ext; apply one_smul)
      (by intro x y; ext; apply mul_smul)
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ N, a ≠ (0 : M) := by
    by_contra! h'
    apply hN
    rwa [eq_bot_iff]
  have : Function.Injective f := by
    change Function.Injective f.toLinearMap
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro s hs
    have : s.1 • a = 0 := congr_arg Subtype.val (LinearMap.congr_fun hs ⟨a, ha₁⟩)
    exact Subtype.ext ((smul_eq_zero_iff_left ha₂).1 this)
  change IsIntegral R (A'.val ⟨x, hx⟩)
  rw [isIntegral_algHom_iff A'.val Subtype.val_injective, ← isIntegral_algHom_iff f this]
  have : Module.Finite R N := by rwa [Module.Finite.iff_fg]
  apply Algebra.IsIntegral.isIntegral

variable {f}

@[stacks 00GK]
/-
**RingHom.Finite.to_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.Finite.to_isIntegral (h : f.Finite) : f.IsIntegral
参数：h : f.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.of_mem_of_fg`：IsIntegral.of_mem_of_fg (S : Subalgebra R B) (H
S : S.toSubmodule.FG) (x : B) (hx : x in S) : IsIntegral R x
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
· 使用定理 `trivial`：True
-/
theorem RingHom.Finite.to_isIntegral (h : f.Finite) : f.IsIntegral :=
  letI := f.toAlgebra
  fun _ ↦ IsIntegral.of_mem_of_fg ⊤ h.1 _ trivial

alias RingHom.IsIntegral.of_finite := RingHom.Finite.to_isIntegral

variable (f)
/-
**RingHom.IsIntegralElem.of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegralElem.of_mem_closure {x y z : S} (hx : f.IsIntegralElem x
) (hy : f.IsIntegralElem y) (hz : z in Subring.closure ({x, y} : Set S)) : f.IsI
ntegralElem z
参数：hx : f.IsIntegralElem x；hy : f.IsIntegralElem y；hz : z in Subring.closure ({x
, y} : Set S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.FG.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R
] [inst_1 : Semiring A] [inst_2 : Algebra R A]   {M N : Submodule R A}, M.FG → N
.FG → …
· 使用定理 `IsIntegral.fg_adjoin_singleton`：IsIntegral.fg_adjoin_singleton [Algebra 
R B] {x : B} (hx : IsIntegral R x) : (Algebra.adjoin R {x}).toSubmodule.FG
· 使用定理 `IsIntegral.of_mem_of_fg`：IsIntegral.of_mem_of_fg (S : Subalgebra R B) (H
S : S.toSubmodule.FG) (x : B) (hx : x in S) : IsIntegral R x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_union`：singleton_union : {a} union s = insert a s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_union_coe_submodule`：adjoin_union_coe_submodule : Subalge
bra.toSubmodule (adjoin R (s union t)) = Subalgebra.toSubmodule (adjoin R s) * S
ubalgebra.toSubmodule (a…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.mem_adjoin_iff`：mem_adjoin_iff {s : Set A} {x : A} : x in adjoin
 R s ↔ x in Subring.closure (Set.range (algebraMap R A) union s)
· 使用定理 `Subring.closure_mono`：closure_mono ⦃s t : Set R⦄ (h : s subseteq t) : cl
osure s <= closure t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
theorem RingHom.IsIntegralElem.of_mem_closure {x y z : S} (hx : f.IsIntegralElem x)
    (hy : f.IsIntegralElem y) (hz : z ∈ Subring.closure ({x, y} : Set S)) : f.IsIntegralElem z := by
  let : Algebra R S := f.toAlgebra
  have := (IsIntegral.fg_adjoin_singleton hx).mul (IsIntegral.fg_adjoin_singleton hy)
  rw [← Algebra.adjoin_union_coe_submodule, Set.singleton_union] at this
  exact
    IsIntegral.of_mem_of_fg (Algebra.adjoin R {x, y}) this z
      (Algebra.mem_adjoin_iff.2 <| Subring.closure_mono Set.subset_union_right hz)

nonrec theorem IsIntegral.of_mem_closure {x y z : A} (hx : IsIntegral R x) (hy : IsIntegral R y)
    (hz : z ∈ Subring.closure ({x, y} : Set A)) : IsIntegral R z :=
  hx.of_mem_closure (algebraMap R A) hy hz

variable (f : R →+* B)
/-
**RingHom.IsIntegralElem.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegralElem.add (f : R ->+* S) {x y : S} (hx : f.IsIntegralElem
 x) (hy : f.IsIntegralElem y) : f.IsIntegralElem (x + y)
参数：f : R ->+* S；hx : f.IsIntegralElem x；hy : f.IsIntegralElem y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsIntegralElem.of_mem_closure`：RingHom.IsIntegralElem.of_mem_clo
sure {x y z : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) (hz : z in 
Subring.closure ({x, y} : S…
· 使用定理 `Subring.add_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) 
{x y : R}, x ∈ s → y ∈ s → x + y ∈ s
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
-/
theorem RingHom.IsIntegralElem.add (f : R →+* S) {x y : S}
    (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x + y) :=
  hx.of_mem_closure f hy <|
    Subring.add_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl))

nonrec theorem IsIntegral.add {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x + y) :=
  hx.add (algebraMap R A) hy

variable (f : R →+* S)

-- can be generalized to noncommutative S.
/-
**RingHom.IsIntegralElem.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegralElem.neg {x : S} (hx : f.IsIntegralElem x) : f.IsIntegra
lElem (-x)
参数：hx : f.IsIntegralElem x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsIntegralElem.of_mem_closure`：RingHom.IsIntegralElem.of_mem_clo
sure {x y z : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) (hz : z in 
Subring.closure ({x, y} : S…
· 使用定理 `Subring.neg_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) 
{x : R}, x ∈ s → -x ∈ s
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
-/
theorem RingHom.IsIntegralElem.neg {x : S} (hx : f.IsIntegralElem x) : f.IsIntegralElem (-x) :=
  hx.of_mem_closure f hx (Subring.neg_mem _ (Subring.subset_closure (Or.inl rfl)))
/-
**RingHom.IsIntegralElem.of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegralElem.of_neg {x : S} (h : f.IsIntegralElem (-x)) : f.IsIn
tegralElem x
参数：h : f.IsIntegralElem (-x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsIntegralElem.neg`：RingHom.IsIntegralElem.neg {x : S} (hx : f.I
sIntegralElem x) : f.IsIntegralElem (-x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem RingHom.IsIntegralElem.of_neg {x : S} (h : f.IsIntegralElem (-x)) : f.IsIntegralElem x :=
  neg_neg x ▸ h.neg

@[simp]
/-
**RingHom.IsIntegralElem.neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegralElem.neg_iff {x : S} : f.IsIntegralElem (-x) ↔ f.IsInteg
ralElem x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsIntegralElem.of_neg`：RingHom.IsIntegralElem.of_neg {x : S} (h 
: f.IsIntegralElem (-x)) : f.IsIntegralElem x
· 使用定理 `RingHom.IsIntegralElem.neg`：RingHom.IsIntegralElem.neg {x : S} (hx : f.I
sIntegralElem x) : f.IsIntegralElem (-x)
-/
theorem RingHom.IsIntegralElem.neg_iff {x : S} : f.IsIntegralElem (-x) ↔ f.IsIntegralElem x :=
  ⟨fun h => h.of_neg, fun h => h.neg⟩
/-
**IsIntegral.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.neg {x : B} (hx : IsIntegral R x) : IsIntegral R (-x)
参数：hx : IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.of_mem_of_fg`：IsIntegral.of_mem_of_fg (S : Subalgebra R B) (H
S : S.toSubmodule.FG) (x : B) (hx : x in S) : IsIntegral R x
· 使用定理 `IsIntegral.fg_adjoin_singleton`：IsIntegral.fg_adjoin_singleton [Algebra 
R B] {x : B} (hx : IsIntegral R x) : (Algebra.adjoin R {x}).toSubmodule.FG
· 使用定理 `Subalgebra.neg_mem`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] (S : Subalgebra R A) {x : A},   x ∈ S → -x 
∈ S
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem IsIntegral.neg {x : B} (hx : IsIntegral R x) : IsIntegral R (-x) :=
  .of_mem_of_fg _ hx.fg_adjoin_singleton _ (Subalgebra.neg_mem _ <| Algebra.subset_adjoin rfl)
/-
**IsIntegral.of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.of_neg {x : B} (hx : IsIntegral R (-x)) : IsIntegral R x
参数：hx : IsIntegral R (-x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.neg`：IsIntegral.neg {x : B} (hx : IsIntegral R x) : IsIntegra
l R (-x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem IsIntegral.of_neg {x : B} (hx : IsIntegral R (-x)) : IsIntegral R x :=
  neg_neg x ▸ hx.neg

@[simp]
/-
**IsIntegral.neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.neg_iff {x : B} : IsIntegral R (-x) ↔ IsIntegral R x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.of_neg`：IsIntegral.of_neg {x : B} (hx : IsIntegral R (-x)) : 
IsIntegral R x
· 使用定理 `IsIntegral.neg`：IsIntegral.neg {x : B} (hx : IsIntegral R x) : IsIntegra
l R (-x)
-/
theorem IsIntegral.neg_iff {x : B} : IsIntegral R (-x) ↔ IsIntegral R x :=
  ⟨IsIntegral.of_neg, IsIntegral.neg⟩
/-
**RingHom.IsIntegralElem.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegralElem.sub {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsI
ntegralElem y) : f.IsIntegralElem (x - y)
参数：hx : f.IsIntegralElem x；hy : f.IsIntegralElem y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `RingHom.IsIntegralElem.add`：RingHom.IsIntegralElem.add (f : R ->+* S) {x
 y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) : f.IsIntegralElem (
x + y)
· 使用定理 `RingHom.IsIntegralElem.neg`：RingHom.IsIntegralElem.neg {x : S} (hx : f.I
sIntegralElem x) : f.IsIntegralElem (-x)
-/
theorem RingHom.IsIntegralElem.sub {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add f (hy.neg f)

nonrec theorem IsIntegral.sub {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x - y) :=
  hx.sub (algebraMap R A) hy
/-
**RingHom.IsIntegralElem.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegralElem.mul {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsI
ntegralElem y) : f.IsIntegralElem (x * y)
参数：hx : f.IsIntegralElem x；hy : f.IsIntegralElem y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsIntegralElem.of_mem_closure`：RingHom.IsIntegralElem.of_mem_clo
sure {x y z : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) (hz : z in 
Subring.closure ({x, y} : S…
· 使用定理 `Subring.mul_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) 
{x y : R}, x ∈ s → y ∈ s → x * y ∈ s
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
-/
theorem RingHom.IsIntegralElem.mul {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x * y) :=
  hx.of_mem_closure f hy
    (Subring.mul_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl)))

nonrec theorem IsIntegral.mul {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x * y) :=
  hx.mul (algebraMap R A) hy
/-
**IsIntegral.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.smul {R} [CommSemiring R] [Algebra R B] [Algebra S B] [Algebra 
R S] [IsScalarTower R S B] {x : B} (r : R) (hx : IsIntegral S x) : IsIntegral S 
(r • x)
参数：r : R；hx : IsIntegral S x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.of_mem_of_fg`：IsIntegral.of_mem_of_fg (S : Subalgebra R B) (H
S : S.toSubmodule.FG) (x : B) (hx : x in S) : IsIntegral R x
· 使用定理 `IsIntegral.fg_adjoin_singleton`：IsIntegral.fg_adjoin_singleton [Algebra 
R B] {x : B} (hx : IsIntegral R x) : (Algebra.adjoin R {x}).toSubmodule.FG
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem IsIntegral.smul {R} [CommSemiring R] [Algebra R B] [Algebra S B] [Algebra R S]
    [IsScalarTower R S B] {x : B} (r : R) (hx : IsIntegral S x) : IsIntegral S (r • x) :=
  .of_mem_of_fg _ hx.fg_adjoin_singleton _ <| by
    rw [← algebraMap_smul S]; apply Subalgebra.smul_mem; exact Algebra.subset_adjoin rfl
/-
**isIntegral_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_intCast (n : Int) : IsIntegral R (n : B)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `isIntegral_algebraMap`：isIntegral_algebraMap {x : R} : IsIntegral R (alg
ebraMap R A x)
-/
theorem isIntegral_intCast (n : ℤ) : IsIntegral R (n : B) := by
  rw [← map_intCast (_ : R →+* B) n]
  exact isIntegral_algebraMap
/-
**isIntegral_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_natCast (a : Nat) : IsIntegral R (a : B)
参数：a : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `isIntegral_intCast`：isIntegral_intCast (n : Int) : IsIntegral R (n : B)
-/
theorem isIntegral_natCast (a : ℕ) : IsIntegral R (a : B) := by
  rw [← Int.cast_natCast]
  exact isIntegral_intCast a

variable (R A)

/-- The integral closure of `R` in an `R`-algebra `A`. -/
/-
**integralClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：integralClosure : Subalgebra R A where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `IsIntegral.add`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …

--- 原说明 ---
The integral closure of `R` in an `R`-algebra `A`.
-/
def integralClosure : Subalgebra R A where
  carrier := { r | IsIntegral R r }
  zero_mem' := isIntegral_zero
  one_mem' := isIntegral_one
  add_mem' := IsIntegral.add
  mul_mem' := IsIntegral.mul
  algebraMap_mem' _ := isIntegral_algebraMap
/-
**mem_integralClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_integralClosure_iff {a : A} : a in integralClosure R A ↔ IsIntegral R 
a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_integralClosure_iff {a : A} : a ∈ integralClosure R A ↔ IsIntegral R a :=
  Iff.rfl

variable {R} {A B : Type*} [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- Product of two integral algebras is an integral algebra. -/
/-
**Algebra.IsIntegral.prod** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.prod [Algebra.IsIntegral R A] [Algebra.IsIntegral R B] 
: Algebra.IsIntegral R (A × B)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Algebra.isIntegral_def`：Algebra.isIntegral_def : Algebra.IsIntegral R A 
↔ forall x : A, IsIntegral R x
· 使用定理 `IsIntegral.pair`：IsIntegral.pair {x : A × B} (hx₁ : IsIntegral R x.1) (h
x₂ : IsIntegral R x.2) : IsIntegral R x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
Product of two integral algebras is an integral algebra.
-/
instance Algebra.IsIntegral.prod [Algebra.IsIntegral R A] [Algebra.IsIntegral R B] :
    Algebra.IsIntegral R (A × B) :=
  Algebra.isIntegral_def.mpr fun x ↦
    (Algebra.isIntegral_def.mp ‹_› x.1).pair (Algebra.isIntegral_def.mp ‹_› x.2)

end

section TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A]

open TensorProduct

/-
**IsIntegral.tmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.tmul [Ring B] [Algebra R A] [Algebra R B] (x : A) {y : B} (h : 
IsIntegral R y) : IsIntegral A (x otimesₜ[R] y)
参数：x : A；h : IsIntegral R y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `IsIntegral.smul`：IsIntegral.smul {R} [CommSemiring R] [Algebra R B] [Alg
ebra S B] [Algebra R S] [IsScalarTower R S B] {x : B} (r : R) (hx : IsIntegral S
 x) :…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsIntegral.map_of_comp_eq`：IsIntegral.map_of_comp_eq {R S T U : Type*} [
CommRing R] [Ring S] [CommRing T] [Ring U] [Algebra R S] [Algebra T U] (φ : R ->
+* T) (ψ : S ->…
· 使用定理 `Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap`：includeLeftRin
gHom_comp_algebraMap : (includeLeftRingHom.comp (algebraMap R A) : R ->+* A otim
es[R] B) = includeRight.toRingHom.comp (algebr…
-/
theorem IsIntegral.tmul [Ring B] [Algebra R A] [Algebra R B]
    (x : A) {y : B} (h : IsIntegral R y) : IsIntegral A (x ⊗ₜ[R] y) := by
  rw [← mul_one x, ← smul_eq_mul, ← smul_tmul']
  exact smul _ (h.map_of_comp_eq (algebraMap R A)
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)

variable (R A B)
/-
**Algebra.IsIntegral.tensorProduct** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.tensorProduct [CommRing B] [Algebra R A] [Algebra R B] 
[int : Algebra.IsIntegral R B] : Algebra.IsIntegral A (A otimes[R] B) where isIn
tegral p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `isIntegral_zero`：isIntegral_zero [Algebra R B] : IsIntegral R (0 : B)
· 使用定理 `IsIntegral.tmul`：IsIntegral.tmul [Ring B] [Algebra R A] [Algebra R B] (x
 : A) {y : B} (h : IsIntegral R y) : IsIntegral A (x otimesₜ[R] y)
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `IsIntegral.add`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
-/
instance Algebra.IsIntegral.tensorProduct [CommRing B]
    [Algebra R A] [Algebra R B] [int : Algebra.IsIntegral R B] :
    Algebra.IsIntegral A (A ⊗[R] B) where
  isIntegral p := p.induction_on isIntegral_zero (fun _ s ↦ .tmul _ <| int.1 s) (fun _ _ ↦ .add)

end TensorProduct

section MulSemiringAction

variable {G R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [Group G] [MulSemiringAction G K] [SMulCommClass G R K]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulSemiringAction G (integralClosure R K) where
  smul := fun g x ↦ ⟨g • (x : K), x.2.map (MulSemiringAction.toAlgHom R K g)⟩
  one_smul x := by ext; exact one_smul G (x : K)
  mul_smul g h x := by ext; exact mul_smul g h (x : K)
  smul_zero g := by ext; exact smul_zero g
  smul_add g x y := by ext; exact smul_add g (x : K) (y : K)
  smul_one g := by ext; exact smul_one g
  smul_mul g x y := by ext; exact smul_mul' g (x : K) (y : K)

@[simp]
/-
**integralClosure.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integralClosure.coe_smul (g : G) (k : integralClosure R K) : (g • k : inte
gralClosure R K) = g • (k : K)
参数：g : G；k : integralClosure R K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integralClosure.coe_smul (g : G) (k : integralClosure R K) :
    (g • k : integralClosure R K) = g • (k : K) := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass G R (integralClosure R K) where
  smul_comm g r k := Subtype.ext (smul_comm g r (k : K))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulDistribClass G (integralClosure R K) K where
  smul_distrib_smul g r k := smul_mul' g (r : K) k

end MulSemiringAction

