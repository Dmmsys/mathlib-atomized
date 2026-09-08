/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.RingTheory.Ideal.Span

/-!
# The basis of ideals

Some results involving `Ideal` and `Basis`.
-/

@[expose] public section

open Module

namespace Ideal

variable {ι R S : Type*} [CommSemiring R] [CommRing S] [IsDomain S] [Algebra R S]

/-- A basis on `S` gives a basis on `Ideal.span {x}`, by multiplying everything by `x`. -/
/-
**Ideal.basisSpanSingleton** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：basisSpanSingleton (b : Basis ι R S) {x : S} (hx : x != 0) : Basis ι R (sp
an ({x} : Set S))
参数：b : Basis ι R S；hx : x != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A basis on `S` gives a basis on `Ideal.span {x}`, by multiplying everything by `
x`.
-/
noncomputable def basisSpanSingleton (b : Basis ι R S) {x : S} (hx : x ≠ 0) :
    Basis ι R (span ({x} : Set S)) :=
  b.map <|
    LinearEquiv.ofInjective (LinearMap.mulLeft R x) (mul_right_injective₀ hx) ≪≫ₗ
        LinearEquiv.ofEq _ _
          (by
            ext
            simp [mem_span_singleton', mul_comm]) ≪≫ₗ
      (Submodule.restrictScalarsEquiv R S S (Ideal.span ({x} : Set S))).restrictScalars R

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Ideal.basisSpanSingleton_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：basisSpanSingleton_apply (b : Basis ι R S) {x : S} (hx : x != 0) (i : ι) :
 (basisSpanSingleton b hx i : S) = x * b i
参数：b : Basis ι R S；hx : x != 0；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.restrictScalars_apply`：∀ (R : Type u_1) {S : Type u_4} {M : 
Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : 
AddCommMonoid M] [inst_…
· 使用定理 `Submodule.restrictScalarsEquiv_apply`：∀ (S : Type u_1) (R : Type u_2) (M
 : Type u_3) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S
]   [inst_3 : _root_.Modul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basisSpanSingleton_apply (b : Basis ι R S) {x : S} (hx : x ≠ 0) (i : ι) :
    (basisSpanSingleton b hx i : S) = x * b i := by
  simp only [basisSpanSingleton, Basis.map_apply, LinearEquiv.trans_apply,
    Submodule.restrictScalarsEquiv_apply, LinearEquiv.ofInjective_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.restrictScalars_apply, LinearMap.mulLeft_apply]

@[simp]
/-
**Ideal.constr_basisSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：constr_basisSpanSingleton {N : Type*} [Semiring N] [Module N S] [SMulCommC
lass R N S] (b : Basis ι R S) {x : S} (hx : x != 0) : (b.constr N).toFun (((↑) :
 _ -> S) ∘ (basisSpanSingleton b hx)) = Algebra.lmul R S x
参数：b : Basis ι R S；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'
· 使用定理 `Ideal.basisSpanSingleton_apply`：basisSpanSingleton_apply (b : Basis ι R 
S) {x : S} (hx : x != 0) (i : ι) : (basisSpanSingleton b hx i : S) = x * b i
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constr_basisSpanSingleton {N : Type*} [Semiring N] [Module N S] [SMulCommClass R N S]
    (b : Basis ι R S) {x : S} (hx : x ≠ 0) :
    (b.constr N).toFun (((↑) : _ → S) ∘ (basisSpanSingleton b hx)) = Algebra.lmul R S x :=
  b.ext fun i => by simp

end Ideal

/-- If `I : Ideal S` has a basis over `R`,
`x ∈ I` iff it is a linear combination of basis vectors. -/
/-
**Basis.mem_ideal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Basis.mem_ideal_iff {ι R S : Type*} [CommSemiring R] [Semiring S] [Algebra
 R S] {I : Ideal S} (b : Basis ι R I) {x : S} : x in I ↔ exists c : ι ->₀ R, x =
 Finsupp.sum c fun i x => x • (b i : S)
参数：b : Basis ι R I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Basis.mem_submodule_iff`：mem_submodule_iff {P : Submodule R M} (b
 : Basis ι R P) {x : M} : x in P ↔ exists c : ι ->₀ R, x = Finsupp.sum c fun i x
 => x • (b i : M)
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Submodule.restrictScalars.isScalarTower`：∀ (S : Type u_1) (R : Type u_2)
 (M : Type u_3) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semirin
g S]   [inst_3 : _root_.Modul…

--- 原说明 ---
If `I : Ideal S` has a basis over `R`,
`x ∈ I` iff it is a linear combination of basis vectors.
-/
theorem Basis.mem_ideal_iff {ι R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {I : Ideal S} (b : Basis ι R I) {x : S} :
    x ∈ I ↔ ∃ c : ι →₀ R, x = Finsupp.sum c fun i x => x • (b i : S) :=
  (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff

/-- If `I : Ideal S` has a finite basis over `R`,
`x ∈ I` iff it is a linear combination of basis vectors. -/
/-
**Basis.mem_ideal_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Basis.mem_ideal_iff' {ι R S : Type*} [Fintype ι] [CommSemiring R] [Semirin
g S] [Algebra R S] {I : Ideal S} (b : Basis ι R I) {x : S} : x in I ↔ exists c :
 ι -> R, x = ∑ i, c i • (b i : S)
参数：b : Basis ι R I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Basis.mem_submodule_iff'`：mem_submodule_iff' [Fintype ι] {P : Sub
module R M} (b : Basis ι R P) {x : M} : x in P ↔ exists c : ι -> R, x = ∑ i, c i
 • (b i : M)
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Submodule.restrictScalars.isScalarTower`：∀ (S : Type u_1) (R : Type u_2)
 (M : Type u_3) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semirin
g S]   [inst_3 : _root_.Modul…

--- 原说明 ---
If `I : Ideal S` has a finite basis over `R`,
`x ∈ I` iff it is a linear combination of basis vectors.
-/
theorem Basis.mem_ideal_iff' {ι R S : Type*} [Fintype ι] [CommSemiring R] [Semiring S] [Algebra R S]
    {I : Ideal S} (b : Basis ι R I) {x : S} : x ∈ I ↔ ∃ c : ι → R, x = ∑ i, c i • (b i : S) :=
  (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff'
