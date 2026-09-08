/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# Linear independence of transcendental elements

## Main result

* `Transcendental.linearIndependent_sub_inv`: let `x : E` transcendental over `F`,
  then `{(x - a)⁻¹ | a : F}` is linearly independent over `F`.
-/

public section

open Polynomial

section

/-- If `E / F` is a field extension, `x` is an element of `E` transcendental over `F`,
then `{(x - a)⁻¹ | a : F}` is linearly independent over `F`. -/
/-
**Transcendental.linearIndependent_sub_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Transcendental.linearIndependent_sub_inv {F E : Type*} [Field F] [Field E]
 [Algebra F E] {x : E} (H : Transcendental F x) : LinearIndependent F fun a => (
x - algebraMap F E a)⁻¹
参数：H : Transcendental F x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `transcendental_iff`：transcendental_iff {x : A} : Transcendental R x ↔ fo
rall p : R[X], aeval x p = 0 -> p = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_erase_mul`：prod_erase_mul [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (∏ x in s.erase a, f x) * f a = ∏ x in s, f x
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
If `E / F` is a field extension, `x` is an element of `E` transcendental over `F
`,
then `{(x - a)⁻¹ | a : F}` is linearly independent over `F`.
-/
theorem Transcendental.linearIndependent_sub_inv
    {F E : Type*} [Field F] [Field E] [Algebra F E] {x : E} (H : Transcendental F x) :
    LinearIndependent F fun a ↦ (x - algebraMap F E a)⁻¹ := by
  classical
  rw [transcendental_iff] at H
  refine linearIndependent_iff'.2 fun s m hm i hi ↦ ?_
  have hnz (a : F) : x - algebraMap F E a ≠ 0 := fun h ↦
    X_sub_C_ne_zero a <| H (.X - .C a) (by simp [h])
  let b := s.prod fun j ↦ x - algebraMap F E j
  have h1 : ∀ i ∈ s, m i • (b * (x - algebraMap F E i)⁻¹) =
      m i • (s.erase i).prod fun j ↦ x - algebraMap F E j := fun i hi ↦ by
    simp_rw [b, ← s.prod_erase_mul _ hi, mul_inv_cancel_right₀ (hnz i)]
  replace hm := congr(b * $(hm))
  simp_rw [mul_zero, Finset.mul_sum, mul_smul_comm, Finset.sum_congr rfl h1] at hm
  let p : Polynomial F := s.sum fun i ↦ .C (m i) * (s.erase i).prod fun j ↦ .X - .C j
  replace hm := congr(Polynomial.aeval i $(H p (by simp_rw [← hm, p, map_sum, map_mul, map_prod,
    map_sub, aeval_X, aeval_C, Algebra.smul_def])))
  have h2 : ∀ j ∈ s.erase i, m j * ((s.erase j).prod fun x ↦ i - x) = 0 := fun j hj ↦ by
    have := Finset.mem_erase_of_ne_of_mem (Finset.ne_of_mem_erase hj).symm hi
    simp_rw [← (s.erase j).prod_erase_mul _ this, sub_self, mul_zero]
  simp_rw [map_zero, p, map_sum, map_mul, map_prod, map_sub, aeval_X,
    aeval_C, Algebra.algebraMap_self_apply, ← s.sum_erase_add _ hi,
    Finset.sum_eq_zero h2, zero_add] at hm
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero (Finset.prod_ne_zero_iff.2 fun j hj ↦
    sub_ne_zero.2 (Finset.ne_of_mem_erase hj).symm) hm

end

