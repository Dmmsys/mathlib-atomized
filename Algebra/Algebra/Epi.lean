/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Algebras which are commutative ring epimorphisms
-/

@[expose] public section

noncomputable section
open Function TensorProduct

namespace Algebra

section Semiring

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

/-- A commutative `R`-algebra `A` is epi, if the multiplication map `A ⊗[R] A → A` is injective. -/
/-
**Algebra.IsEpi** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_1) → (A : Type u_2) → [inst : CommSemiring R] → [inst_1 : Semi
ring A] → [Algebra R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commutative `R`-algebra `A` is epi, if the multiplication map `A ⊗[R] A → A` i
s injective.
-/
protected class IsEpi : Prop where
  injective_lift_mul : Injective <| lift <| LinearMap.mul R A

/-- See also `CommRingCat.epi_iff_epi`. -/
/-
**Algebra.isEpi_iff_forall_one_tmul_eq** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：isEpi_iff_forall_one_tmul_eq : Algebra.IsEpi R A ↔ forall a : A, 1 otimesₜ
[R] a = a otimesₜ[R] 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsEpi.injective_lift_mul`：∀ {R : Type u_1} {A : Type u_2} {inst 
: CommSemiring R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra
.IsEpi R A], Function.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
See also `CommRingCat.epi_iff_epi`.
-/
lemma isEpi_iff_forall_one_tmul_eq :
    Algebra.IsEpi R A ↔ ∀ a : A, 1 ⊗ₜ[R] a = a ⊗ₜ[R] 1 := by
  refine ⟨fun h a ↦ IsEpi.injective_lift_mul <| by simp, fun h ↦ ⟨fun x y hxy ↦ ?_⟩⟩
  have h' (x : A ⊗[R] A) : ∃ a : A, x = a ⊗ₜ 1 := by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul u v =>
      use u * v
      calc u ⊗ₜ[R] v = u ⊗ₜ[R] 1 * 1 ⊗ₜ[R] v := by simp
                   _ = u ⊗ₜ[R] 1 * v ⊗ₜ[R] 1 := by rw [h]
                   _ = (u * v) ⊗ₜ[R] 1 := by simp
    | add u v hu hv =>
      obtain ⟨u, rfl⟩ := hu
      obtain ⟨v, rfl⟩ := hv
      exact ⟨u  + v, by simp [add_tmul]⟩
  obtain ⟨a, rfl⟩ := h' x
  obtain ⟨b, rfl⟩ := h' y
  aesop

/-- See also `Algebra.isEpi_iff_surjective_algebraMap_of_finite`. -/
/-
**Algebra.isEpi_of_surjective_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：isEpi_of_surjective_algebraMap (h : Surjective (algebraMap R A)) : Algebra
.IsEpi R A
参数：h : Surjective (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Algebra.isEpi_iff_forall_one_tmul_eq`：isEpi_iff_forall_one_tmul_eq : Alg
ebra.IsEpi R A ↔ forall a : A, 1 otimesₜ[R] a = a otimesₜ[R] 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…

--- 原说明 ---
See also `Algebra.isEpi_iff_surjective_algebraMap_of_finite`.
-/
lemma isEpi_of_surjective_algebraMap (h : Surjective (algebraMap R A)) :
    Algebra.IsEpi R A := by
  refine (isEpi_iff_forall_one_tmul_eq R A).mpr fun a ↦ ?_
  obtain ⟨r, rfl⟩ := h a
  rw [algebraMap_eq_smul_one, smul_tmul]

end Semiring

-- TODO Generalise to any localization
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R A : Type*) [CommRing R] [IsDomain R] [Field A] [Algebra R A] [IsFractionRing R A] :
    Algebra.IsEpi R A := by
  refine (isEpi_iff_forall_one_tmul_eq R A).mpr fun x ↦ ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  set f := algebraMap R A with hf
  replace hb : f b ≠ 0 := by aesop
  calc 1 ⊗ₜ[R] (f a / f b)
       = 1 ⊗ₜ[R] (a • (1 / f b)) := by rw [← smul_div_assoc, algebraMap_eq_smul_one a]
     _ = f a ⊗ₜ[R] (1 / f b) := by rw [← smul_tmul, algebraMap_eq_smul_one a]
     _ = (b • (f a / f b)) ⊗ₜ[R] (1 / f b) := by rw [smul_def, mul_div_cancel₀ _ hb]
     _ = (f a / f b) ⊗ₜ[R] (b • (1 / f b)) := by rw [smul_tmul]
     _ = (f a / f b) ⊗ₜ[R] 1 := by rw [smul_def, mul_div_cancel₀ _ hb]

section Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-
**Algebra.isEpi_iff_surjective_algebraMap_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebra`。
形式化陈述：isEpi_iff_surjective_algebraMap_of_finite [Module.Finite R A] : Algebra.Is
Epi R A ↔ Surjective (algebraMap R A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.Quotient.subsingleton_iff`：∀ {R : Type u_1} {M : Type u_2} [in
st : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submo
dule R M}, Subsingleton (…
· 使用定理 `subsingleton_of_forall_eq`：∀ {α : Sort u_1} (x : α), (∀ (y : α), y = x) 
→ Subsingleton α
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Algebra.isEpi_iff_forall_one_tmul_eq`：isEpi_iff_forall_one_tmul_eq : Alg
ebra.IsEpi R A ↔ forall a : A, 1 otimesₜ[R] a = a otimesₜ[R] 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.map_tmul`：map_tmul (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N
₂) (m : M) (n : N) : map f g (m otimesₜ n) = f m otimesₜ g n
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `false_of_nontrivial_of_subsingleton`：false_of_nontrivial_of_subsingleton
 (α : Type*) [Nontrivial α] [Subsingleton α] : False
· 使用定理 `instNontrivialTensorProduct`：∀ (R : Type u_1) (M : Type u_2) [inst : Com
mRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Module.Finite
 R M] [Nontrivial…
（共 31 条，此处仅展示前 30 条）
-/
lemma isEpi_iff_surjective_algebraMap_of_finite [Module.Finite R A] :
    Algebra.IsEpi R A ↔ Surjective (algebraMap R A) := by
  refine ⟨fun h ↦ ?_, isEpi_of_surjective_algebraMap R A⟩
  let R' := (Algebra.linearMap R A).range
  rcases subsingleton_or_nontrivial (A ⧸ R') with h | _
  · rwa [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top] at h
  have : Subsingleton ((A ⧸ R') ⊗[R] (A ⧸ R')) := by
    refine subsingleton_of_forall_eq 0 fun y ↦ ?_
    induction y with
    | zero => rfl
    | add a b e₁ e₂ => rwa [e₁, zero_add]
    | tmul x y =>
      obtain ⟨x, rfl⟩ := R'.mkQ_surjective x
      obtain ⟨y, rfl⟩ := R'.mkQ_surjective y
      obtain ⟨s, hs⟩ : ∃ s, 1 ⊗ₜ[R] s = x ⊗ₜ[R] y := by
        use x * y
        trans x ⊗ₜ 1 * 1 ⊗ₜ y
        · simp [(isEpi_iff_forall_one_tmul_eq R A).mp]
        · simp
      have : R'.mkQ 1 = 0 := (Submodule.Quotient.mk_eq_zero R').mpr ⟨1, map_one (algebraMap R A)⟩
      rw [← map_tmul R'.mkQ R'.mkQ, ← hs, map_tmul, this, zero_tmul]
  cases false_of_nontrivial_of_subsingleton ((A ⧸ R') ⊗[R] (A ⧸ R'))

@[deprecated (since := "2026-01-13")]
alias _root_.RingHom.surjective_of_tmul_eq_tmul_of_finite :=
  isEpi_iff_surjective_algebraMap_of_finite

end Ring

section CommSemiring

variable (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] [Algebra.IsEpi R A]

variable {A} in
/-
**Algebra.tmul_comm** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：tmul_comm (a b : A) : a otimesₜ[R] b = b otimesₜ[R] a
参数：a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.tmul_eq_smul_one_tmul`：tmul_eq_smul_one_tmul {S : Type*} [
Semiring S] [Module R S] [SMulCommClass R S S] (s : S) (m : M) : s otimesₜ[R] m 
= s • (1 otimesₜ[R] m)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Algebra.isEpi_iff_forall_one_tmul_eq`：isEpi_iff_forall_one_tmul_eq : Alg
ebra.IsEpi R A ↔ forall a : A, 1 otimesₜ[R] a = a otimesₜ[R] 1
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
lemma tmul_comm (a b : A) :
    a ⊗ₜ[R] b = b ⊗ₜ[R] a := by
  have (a b : A) := calc a ⊗ₜ[R] b
      = a • (1 ⊗ₜ[R] b) := by rw [tmul_eq_smul_one_tmul]
    _ = a • (b ⊗ₜ[R] 1) := by rw [(isEpi_iff_forall_one_tmul_eq R A).mp inferInstance b]
    _ = a • (b • (1 ⊗ₜ[R] 1)) := by rw [tmul_eq_smul_one_tmul]
  rw [this a b, this b a, smul_comm]

section Module

variable (M : Type*) [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

set_option backward.isDefEq.respectTransparency false in
/-- If an `R`-algebra `A` is epi, then the scalar multiplication `A ⊗[R] M → M` is injective, for
any `A`-module `M`. -/
/-
**Algebra.injective_lift_lsmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：injective_lift_lsmul : Injective (lift <| LinearMap.restrictScalars₁₂ R R 
(LinearMap.lsmul A M))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Algebra.tmul_comm`：tmul_comm (a b : A) : a otimesₜ[R] b = b otimesₜ[R] a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.restrictScalars₁₂_apply_apply`：∀ {R : Type u_1} {S : Type u_3}
 [inst : Semiring R] [inst_1 : Semiring S] {M : Type u_5} {N : Type u_7} {Pₗ : T
ype u_11}   [inst_2 : AddComm…
· 使用定理 `Function.HasLeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : 
α → β}, Function.HasLeftInverse f → Function.Injective f

--- 原说明 ---
If an `R`-algebra `A` is epi, then the scalar multiplication `A ⊗[R] M → M` is i
njective, for
any `A`-module `M`.
-/
lemma injective_lift_lsmul :
    Injective (lift <| LinearMap.restrictScalars₁₂ R R (LinearMap.lsmul A M)) := by
  /- Morally the proof is to recognise that we can construct the map `A ⊗[R] M → M` as a
  composition of (`A`-linear) equivalences:
  ```
  A ⊗[R] M ≃  A ⊗[R] (A ⊗[A] M)
           ≃ (A ⊗[R] A) ⊗[A] M
           ≃ A ⊗[A] M
           ≃ M
  ```
  However the second equivalence above requires a version of heterogeneous tensor product
  associativity which is problematic in Mathlib because `TensorProduct.leftModule` prioritises the
  left factor in any tensor product. We therefore formalise a slightly lower level proof below. -/
  suffices ∀ (a : A) (m : M), 1 ⊗ₜ[R] (a • m) = a ⊗ₜ[R] m by
    let f : M →ₗ[R] A ⊗[R] M :=
      { toFun m := 1 ⊗ₜ m
        map_add' m n := tmul_add _ _ _
        map_smul' r m := tmul_smul _ _ _ }
    have aux : f ∘ₗ (lift <| LinearMap.restrictScalars₁₂ R R (LinearMap.lsmul A M)) = .id := by
      ext a m; simpa using! this a m
    exact HasLeftInverse.injective ⟨f, fun x ↦ congr($aux x)⟩
  intro a m
  let f : A ⊗[R] A →ₗ[R] A ⊗[R] M := lift
    { toFun x :=
      { toFun y := x ⊗ₜ (y • m)
        map_add' := by simp [add_smul, tmul_add]
        map_smul' := by simp }
      map_add' := by intros; ext; simp [add_tmul]
      map_smul' := by intros; ext; simp [smul_tmul'] }
  simpa [f] using! congr_arg f (tmul_comm R 1 a)

/-- A heterogeneous variant of `TensorProduct.lid` when `R → A` is epi. -/
/-
**Algebra._root_.TensorProduct.lid'** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A heterogeneous variant of `TensorProduct.lid` when `R → A` is epi.
-/
def _root_.TensorProduct.lid' : A ⊗[R] M ≃ₗ[A] M :=
  .ofBijective
    (AlgebraTensorModule.lift <| LinearMap.restrictScalarsₗ R A M M A ∘ₗ LinearMap.lsmul A M)
    ⟨injective_lift_lsmul R A M, fun m ↦ ⟨1 ⊗ₜ m, by simp⟩⟩
/-
**Algebra._root_.TensorProduct.lid'_apply_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.TensorProduct.lid'_apply_tmul (a : A) (m : M) :
    TensorProduct.lid' R A M (a ⊗ₜ m) = a • m :=
  rfl
/-
**Algebra._root_.TensorProduct.lid'_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.TensorProduct.lid'_symm_apply (m : M) :
    (TensorProduct.lid' R A M).symm m = 1 ⊗ₜ m :=
  (TensorProduct.lid' R A M).injective <| by simp

end Module

end CommSemiring

end Algebra

