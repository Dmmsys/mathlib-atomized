/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.LinearAlgebra.SModEq.Pointwise
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Functoriality of adic completions

In this file we establish functorial properties of the adic completion.

## Main definitions

- `AdicCauchySequence.map I f`: the linear map on `I`-adic Cauchy sequences induced by `f`
- `AdicCompletion.map I f`: the linear map on `I`-adic completions induced by `f`

## Main results

- `sumEquivOfFintype`: adic completion commutes with finite sums
- `piEquivOfFintype`: adic completion commutes with finite products

-/

@[expose] public section

suppress_compilation

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {P : Type*} [AddCommGroup P] [Module R P]
variable {T : Type*} [AddCommGroup T] [Module (AdicCompletion I R) T]

namespace LinearMap

/-- The induced linear map on the quotients mod `I • ⊤`. -/
/-
**LinearMap.reduceModIdeal** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：reduceModIdeal (f : M ->ₗ[R] N) : M ⧸ (I • ⊤ : Submodule R M) ->ₗ[R ⧸ I] N
 ⧸ (I • ⊤ : Submodule R N)
参数：f : M ->ₗ[R] N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The induced linear map on the quotients mod `I • ⊤`.
-/
def reduceModIdeal (f : M →ₗ[R] N) :
    M ⧸ (I • ⊤ : Submodule R M) →ₗ[R ⧸ I] N ⧸ (I • ⊤ : Submodule R N) :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective <|
    Submodule.mapQ (I • ⊤ : Submodule R M) (I • ⊤ : Submodule R N) f
      (fun x hx ↦ by
        refine Submodule.smul_induction_on hx (fun r hr x _ ↦ ?_) (fun x y hx hy ↦ ?_)
        · simp [Submodule.smul_mem_smul hr Submodule.mem_top]
        · simp [Submodule.add_mem _ hx hy])

@[simp]
/-
**LinearMap.reduceModIdeal_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：reduceModIdeal_apply (f : M ->ₗ[R] N) (x : M) : (f.reduceModIdeal I) (Subm
odule.Quotient.mk (p
参数：f : M ->ₗ[R] N；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem reduceModIdeal_apply (f : M →ₗ[R] N) (x : M) :
    (f.reduceModIdeal I) (Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) x) =
      Submodule.Quotient.mk (p := (I • ⊤ : Submodule R N)) (f x) :=
  rfl

end LinearMap

namespace AdicCompletion

open LinearMap

set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.transitionMap_comp_reduceModIdeal** 是 Mathlib 中的一个定理，位于命名空间 `Ad
icCompletion`。
形式化陈述：transitionMap_comp_reduceModIdeal (f : M ->ₗ[R] N) {m n : Nat} (hmn : m <=
 n) : transitionMap I N hmn ∘ₗ f.reduceModIdeal (I ^ n) = (f.reduceModIdeal (I ^
 m) : _ ->ₗ[R] _) ∘ₗ transitionMap I M hmn
参数：f : M ->ₗ[R] N；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.linearMap_qext`：linearMap_qext ⦃f g : M ⧸ p ->ₛₗ[τ₁₂] M₂⦄ (h :
 f.comp p.mkQ = g.comp p.mkQ) : f = g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Module.IsTorsionBySet.isScalarTower`：∀ {R : Type u_1} {M : Type u_2} [in
st : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {I : Ideal R
}   (hM : Module.IsTorsio…
· 使用引理 `Module.isTorsionBySet_quotient_ideal_smul`：isTorsionBySet_quotient_ideal
_smul : IsTorsionBySet R (M ⧸ I • (⊤ : Submodule R M)) I
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transitionMap_comp_reduceModIdeal (f : M →ₗ[R] N) {m n : ℕ}
    (hmn : m ≤ n) : transitionMap I N hmn ∘ₗ f.reduceModIdeal (I ^ n) =
      (f.reduceModIdeal (I ^ m) : _ →ₗ[R] _) ∘ₗ transitionMap I M hmn := by
  ext x
  simp

namespace AdicCauchySequence

set_option backward.isDefEq.respectTransparency false in
/-- A linear map induces a linear map on adic Cauchy sequences. -/
@[simps]
/-
**AdicCompletion.AdicCauchySequence.map** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletio
n.AdicCauchySequence`。
形式化陈述：map (f : M ->ₗ[R] N) : AdicCauchySequence I M ->ₗ[R] AdicCauchySequence I 
N where toFun a
参数：f : M ->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map induces a linear map on adic Cauchy sequences.
-/
def map (f : M →ₗ[R] N) : AdicCauchySequence I M →ₗ[R] AdicCauchySequence I N where
  toFun a := ⟨fun n ↦ f (a n), fun {m n} hmn ↦ by
    have hm : Submodule.map f (I ^ m • ⊤ : Submodule R M) ≤ (I ^ m • ⊤ : Submodule R N) := by
      rw [Submodule.map_smul'']
      exact smul_mono_right _ le_top
    apply SModEq.mono hm
    apply SModEq.map (a.property hmn) f⟩
  map_add' a b := by ext n; simp
  map_smul' r a := by ext n; simp

variable (M) in
@[simp]
/-
**AdicCompletion.AdicCauchySequence.map_id** 是 Mathlib 中的一个定理，位于命名空间 `AdicComple
tion.AdicCauchySequence`。
形式化陈述：map_id : map I (LinearMap.id (M
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_id : map I (LinearMap.id (M := M)) = LinearMap.id :=
  rfl
/-
**AdicCompletion.AdicCauchySequence.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `AdicComp
letion.AdicCauchySequence`。
形式化陈述：map_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) : map I g ∘ₗ map I f = map I (g
 ∘ₗ f)
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map I g ∘ₗ map I f = map I (g ∘ₗ f) :=
  rfl
/-
**AdicCompletion.AdicCauchySequence.map_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ad
icCompletion.AdicCauchySequence`。
形式化陈述：map_comp_apply (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (a : AdicCauchySequence I
 M) : map I g (map I f a) = map I (g ∘ₗ f) a
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] P；a : AdicCauchySequence I M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_apply (f : M →ₗ[R] N) (g : N →ₗ[R] P) (a : AdicCauchySequence I M) :
    map I g (map I f a) = map I (g ∘ₗ f) a :=
  rfl

@[simp]
/-
**AdicCompletion.AdicCauchySequence.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `AdicComp
letion.AdicCauchySequence`。
形式化陈述：map_zero : map I (0 : M ->ₗ[R] N) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_zero : map I (0 : M →ₗ[R] N) = 0 :=
  rfl

end AdicCauchySequence

/-- A linear map induces a map on adic completions. -/
/-
**AdicCompletion.map** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：map (f : M ->ₗ[R] N) : AdicCompletion I M ->ₗ[AdicCompletion I R] AdicComp
letion I N where __
参数：f : M ->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map induces a map on adic completions.
-/
def map (f : M →ₗ[R] N) :
    AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N where
  __ := AdicCompletion.lift I (fun n ↦ reduceModIdeal (I ^ n) f ∘ₗ AdicCompletion.eval I M n)
    (fun {m n} hmn ↦ by rw [← comp_assoc, AdicCompletion.transitionMap_comp_reduceModIdeal,
        comp_assoc, transitionMap_comp_eval])
  map_smul' r x := by
    ext
    dsimp
    rw [val_smul_eq_evalₐ_smul, val_smul_eq_evalₐ_smul, map_smul]

@[simp]
/-
**AdicCompletion.map_val_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：map_val_apply (f : M ->ₗ[R] N) {n : Nat} (x : AdicCompletion I M) : (map I
 f x).val n = f.reduceModIdeal (I ^ n) (x.val n)
参数：f : M ->ₗ[R] N；x : AdicCompletion I M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_val_apply (f : M →ₗ[R] N) {n : ℕ} (x : AdicCompletion I M) :
    (map I f x).val n = f.reduceModIdeal (I ^ n) (x.val n) :=
  rfl

/-- Equality of maps out of an adic completion can be checked on Cauchy sequences. -/
/-
**AdicCompletion.map_ext** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：map_ext {N} {f g : AdicCompletion I M -> N} (h : forall (a : AdicCauchySeq
uence I M), f (AdicCompletion.mk I M a) = g (AdicCompletion.mk I M a)) : f = g
参数：h : forall (a : AdicCauchySequence I M), f (AdicCompletion.mk I M a) = g (Adi
cCompletion.mk I M a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AdicCompletion.induction_on`：induction_on {p : AdicCompletion I M -> Pro
p} (x : AdicCompletion I M) (h : forall (f : AdicCauchySequence I M), p (mk I M 
f)) : p x

--- 原说明 ---
Equality of maps out of an adic completion can be checked on Cauchy sequences.
-/
theorem map_ext {N} {f g : AdicCompletion I M → N}
    (h : ∀ (a : AdicCauchySequence I M),
      f (AdicCompletion.mk I M a) = g (AdicCompletion.mk I M a)) :
    f = g := by
  ext x
  apply induction_on I M x h

/-- Equality of linear maps out of an adic completion can be checked on Cauchy sequences. -/
@[ext]
/-
**AdicCompletion.map_ext'** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：map_ext' {f g : AdicCompletion I M ->ₗ[AdicCompletion I R] T} (h : forall 
(a : AdicCauchySequence I M), f (AdicCompletion.mk I M a) = g (AdicCompletion.mk
 I M a)) : f = g
参数：h : forall (a : AdicCauchySequence I M), f (AdicCompletion.mk I M a) = g (Adi
cCompletion.mk I M a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `AdicCompletion.induction_on`：induction_on {p : AdicCompletion I M -> Pro
p} (x : AdicCompletion I M) (h : forall (f : AdicCauchySequence I M), p (mk I M 
f)) : p x

--- 原说明 ---
Equality of linear maps out of an adic completion can be checked on Cauchy seque
nces.
-/
theorem map_ext' {f g : AdicCompletion I M →ₗ[AdicCompletion I R] T}
    (h : ∀ (a : AdicCauchySequence I M),
      f (AdicCompletion.mk I M a) = g (AdicCompletion.mk I M a)) :
    f = g := by
  ext x
  apply induction_on I M x h

/-- Equality of linear maps out of an adic completion can be checked on Cauchy sequences. -/
@[ext]
/-
**AdicCompletion.map_ext''** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：map_ext'' {f g : AdicCompletion I M ->ₗ[R] N} (h : f.comp (AdicCompletion.
mk I M) = g.comp (AdicCompletion.mk I M)) : f = g
参数：h : f.comp (AdicCompletion.mk I M) = g.comp (AdicCompletion.mk I M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `AdicCompletion.induction_on`：induction_on {p : AdicCompletion I M -> Pro
p} (x : AdicCompletion I M) (h : forall (f : AdicCauchySequence I M), p (mk I M 
f)) : p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…

--- 原说明 ---
Equality of linear maps out of an adic completion can be checked on Cauchy seque
nces.
-/
theorem map_ext'' {f g : AdicCompletion I M →ₗ[R] N}
    (h : f.comp (AdicCompletion.mk I M) = g.comp (AdicCompletion.mk I M)) :
    f = g := by
  ext x
  apply induction_on I M x (fun a ↦ LinearMap.ext_iff.mp h a)

variable (M) in
@[simp]
/-
**AdicCompletion.map_id** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：map_id : map I (LinearMap.id (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AdicCompletion.map_ext'`：map_ext' {f g : AdicCompletion I M ->ₗ[AdicComp
letion I R] T} (h : forall (a : AdicCauchySequence I M), f (AdicCompletion.mk I 
M a) = g (Adi…
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `AdicCompletion.mk_apply_coe`：∀ {R : Type u_1} [inst : CommRing R] (I : I
deal R) (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   
(f : AdicCompleti…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_id :
    map I (LinearMap.id (M := M)) =
      LinearMap.id (R := AdicCompletion I R) (M := AdicCompletion I M) := by
  ext a n
  simp
/-
**AdicCompletion.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：map_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) : map I g ∘ₗ map I f = map I (g
 ∘ₗ f)
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AdicCompletion.map_ext'`：map_ext' {f g : AdicCompletion I M ->ₗ[AdicComp
letion I R] T} (h : forall (a : AdicCauchySequence I M), f (AdicCompletion.mk I 
M a) = g (Adi…
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `AdicCompletion.mk_apply_coe`：∀ {R : Type u_1} [inst : CommRing R] (I : I
deal R) (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   
(f : AdicCompleti…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map I g ∘ₗ map I f = map I (g ∘ₗ f) := by
  ext
  simp
/-
**AdicCompletion.map_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：map_comp_apply (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (x : AdicCompletion I M) 
: map I g (map I f x) = map I (g ∘ₗ f) x
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] P；x : AdicCompletion I M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdicCompletion.map_comp`：map_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) : ma
p I g ∘ₗ map I f = map I (g ∘ₗ f)
-/
theorem map_comp_apply (f : M →ₗ[R] N) (g : N →ₗ[R] P) (x : AdicCompletion I M) :
    map I g (map I f x) = map I (g ∘ₗ f) x := by
  change (map I g ∘ₗ map I f) x = map I (g ∘ₗ f) x
  rw [map_comp]

@[simp]
/-
**AdicCompletion.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：map_mk (f : M ->ₗ[R] N) (a : AdicCauchySequence I M) : map I f (AdicComple
tion.mk I M a) = AdicCompletion.mk I N (AdicCauchySequence.map I f a)
参数：f : M ->ₗ[R] N；a : AdicCauchySequence I M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mk (f : M →ₗ[R] N) (a : AdicCauchySequence I M) :
    map I f (AdicCompletion.mk I M a) =
      AdicCompletion.mk I N (AdicCauchySequence.map I f a) :=
  rfl

@[simp]
/-
**AdicCompletion.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：map_zero : map I (0 : M ->ₗ[R] N) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AdicCompletion.map_ext'`：map_ext' {f g : AdicCompletion I M ->ₗ[AdicComp
letion I R] T} (h : forall (a : AdicCauchySequence I M), f (AdicCompletion.mk I 
M a) = g (Adi…
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
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
-/
theorem map_zero : map I (0 : M →ₗ[R] N) = 0 := by
  ext
  simp
/-
**AdicCompletion.map_of** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：map_of (f : M ->ₗ[R] N) (x : M) : map I f (of I M x) = of I N (f x)
参数：f : M ->ₗ[R] N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_of (f : M →ₗ[R] N) (x : M) : map I f (of I M x) = of I N (f x) :=
  rfl

/-- A linear equiv induces a linear equiv on adic completions. -/
/-
**AdicCompletion.congr** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：congr (f : M ≃ₗ[R] N) : AdicCompletion I M ≃ₗ[AdicCompletion I R] AdicComp
letion I N
参数：f : M ≃ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equiv induces a linear equiv on adic completions.
-/
def congr (f : M ≃ₗ[R] N) :
    AdicCompletion I M ≃ₗ[AdicCompletion I R] AdicCompletion I N :=
  LinearEquiv.ofLinearMap (map I f)
    (map I f.symm) (by simp [map_comp]) (by simp [map_comp])

@[simp]
/-
**AdicCompletion.congr_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：congr_apply (f : M ≃ₗ[R] N) (x : AdicCompletion I M) : congr I f x = map I
 f x
参数：f : M ≃ₗ[R] N；x : AdicCompletion I M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_apply (f : M ≃ₗ[R] N) (x : AdicCompletion I M) :
    congr I f x = map I f x :=
  rfl

@[simp]
/-
**AdicCompletion.congr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：congr_symm_apply (f : M ≃ₗ[R] N) (x : AdicCompletion I N) : (congr I f).sy
mm x = map I f.symm x
参数：f : M ≃ₗ[R] N；x : AdicCompletion I N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_symm_apply (f : M ≃ₗ[R] N) (x : AdicCompletion I N) :
    (congr I f).symm x = map I f.symm x :=
  rfl

section Families

/-! ### Adic completion in families

In this section we consider a family `M : ι → Type*` of `R`-modules. Purely from
the formal properties of adic completions we obtain two canonical maps

- `AdicCompletion I (∀ j, M j) →ₗ[R] ∀ j, AdicCompletion I (M j)`
- `(⨁ j, (AdicCompletion I (M j))) →ₗ[R] AdicCompletion I (⨁ j, M j)`

If `ι` is finite, both are isomorphisms and, modulo
the equivalence `⨁ j, (AdicCompletion I (M j)` and `∀ j, AdicCompletion I (M j)`,
inverse to each other.

-/

variable {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)]

section Pi

/-- The canonical map from the adic completion of the product to the product of the
adic completions. -/
@[simps!]
/-
**AdicCompletion.pi** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：pi : AdicCompletion I (forall j, M j) ->ₗ[AdicCompletion I R] forall j, Ad
icCompletion I (M j)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the adic completion of the product to the product of the
adic completions.
-/
def pi : AdicCompletion I (∀ j, M j) →ₗ[AdicCompletion I R] ∀ j, AdicCompletion I (M j) :=
  LinearMap.pi (fun j ↦ map I (LinearMap.proj j))

end Pi

section Sum

open DirectSum

/-- The canonical map from the sum of the adic completions to the adic completion
of the sum. -/
/-
**AdicCompletion.sum** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：sum [DecidableEq ι] : (⨁ j, (AdicCompletion I (M j))) ->ₗ[AdicCompletion I
 R] AdicCompletion I (⨁ j, M j)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the sum of the adic completions to the adic completion
of the sum.
-/
def sum [DecidableEq ι] :
    (⨁ j, (AdicCompletion I (M j))) →ₗ[AdicCompletion I R] AdicCompletion I (⨁ j, M j) :=
  toModule (AdicCompletion I R) ι (AdicCompletion I (⨁ j, M j))
    (fun j ↦ map I (lof R ι M j))

@[simp]
/-
**AdicCompletion.sum_lof** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：sum_lof [DecidableEq ι] (j : ι) (x : AdicCompletion I (M j)) : sum I M ((D
irectSum.lof (AdicCompletion I R) ι (fun i => AdicCompletion I (M i)) j) x) = ma
p I (lof R ι M j) x
参数：j : ι；x : AdicCompletion I (M j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.toModule_lof`：toModule_lof (i) (x : M i) : toModule R ι N φ (l
of R ι M i x) = φ i x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_lof [DecidableEq ι] (j : ι) (x : AdicCompletion I (M j)) :
    sum I M ((DirectSum.lof (AdicCompletion I R) ι (fun i ↦ AdicCompletion I (M i)) j) x) =
      map I (lof R ι M j) x := by
  simp [sum]

@[simp]
/-
**AdicCompletion.sum_of** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：sum_of [DecidableEq ι] (j : ι) (x : AdicCompletion I (M j)) : sum I M ((Di
rectSum.of (fun i => AdicCompletion I (M i)) j) x) = map I (lof R ι M j) x
参数：j : ι；x : AdicCompletion I (M j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.lof_eq_of`：lof_eq_of (i : ι) (b : M i) : lof R ι M i b = of M 
i b
· 使用定理 `AdicCompletion.sum_lof`：sum_lof [DecidableEq ι] (j : ι) (x : AdicComplet
ion I (M j)) : sum I M ((DirectSum.lof (AdicCompletion I R) ι (fun i => AdicComp
letion I (M …
-/
theorem sum_of [DecidableEq ι] (j : ι) (x : AdicCompletion I (M j)) :
    sum I M ((DirectSum.of (fun i ↦ AdicCompletion I (M i)) j) x) =
      map I (lof R ι M j) x := by
  rw [← lof_eq_of R]
  apply sum_lof

variable [Fintype ι]

/-- If `ι` is finite, we use the equivalence of sum and product to obtain an inverse for
`AdicCompletion.sum` from `AdicCompletion.pi`. -/
/-
**AdicCompletion.sumInv** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：sumInv : AdicCompletion I (⨁ j, M j) ->ₗ[AdicCompletion I R] (⨁ j, (AdicCo
mpletion I (M j)))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ι` is finite, we use the equivalence of sum and product to obtain an inverse
 for
`AdicCompletion.sum` from `AdicCompletion.pi`.
-/
def sumInv : AdicCompletion I (⨁ j, M j) →ₗ[AdicCompletion I R] (⨁ j, (AdicCompletion I (M j))) :=
  letI f := map I (linearEquivFunOnFintype R ι M)
  letI g := linearEquivFunOnFintype (AdicCompletion I R) ι (fun j ↦ AdicCompletion I (M j))
  g.symm.toLinearMap ∘ₗ pi I M ∘ₗ f

@[simp]
/-
**AdicCompletion.component_sumInv** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：component_sumInv (x : AdicCompletion I (⨁ j, M j)) (j : ι) : component (Ad
icCompletion I R) ι _ j (sumInv I M x) = map I (component R ι _ j) x
参数：x : AdicCompletion I (⨁ j, M j)；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AdicCompletion.induction_on`：induction_on {p : AdicCompletion I M -> Pro
p} (x : AdicCompletion I M) (h : forall (f : AdicCauchySequence I M), p (mk I M 
f)) : p x
-/
theorem component_sumInv (x : AdicCompletion I (⨁ j, M j)) (j : ι) :
    component (AdicCompletion I R) ι _ j (sumInv I M x) =
      map I (component R ι _ j) x := by
  apply induction_on I _ x (fun x ↦ ?_)
  rfl

@[simp]
/-
**AdicCompletion.sumInv_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：sumInv_apply (x : AdicCompletion I (⨁ j, M j)) (j : ι) : (sumInv I M x) j 
= map I (component R ι _ j) x
参数：x : AdicCompletion I (⨁ j, M j)；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AdicCompletion.induction_on`：induction_on {p : AdicCompletion I M -> Pro
p} (x : AdicCompletion I M) (h : forall (f : AdicCauchySequence I M), p (mk I M 
f)) : p x
-/
theorem sumInv_apply (x : AdicCompletion I (⨁ j, M j)) (j : ι) :
    (sumInv I M x) j = map I (component R ι _ j) x := by
  apply induction_on I _ x (fun x ↦ ?_)
  rfl

variable [DecidableEq ι]
/-
**AdicCompletion.sumInv_comp_sum** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：sumInv_comp_sum : sumInv I M ∘ₗ sum I M = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.linearMap_ext`：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H :
 forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'
· 使用定理 `AdicCompletion.map_ext'`：map_ext' {f g : AdicCompletion I M ->ₗ[AdicComp
letion I R] T} (h : forall (a : AdicCauchySequence I M), f (AdicCompletion.mk I 
M a) = g (Adi…
· 使用定理 `DirectSum.ext_component`：ext_component {f g : ⨁ i, M i} (h : forall i, c
omponent R ι M i f = component R ι M i g) : f = g
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AdicCompletion.sum_lof`：sum_lof [DecidableEq ι] (j : ι) (x : AdicComplet
ion I (M j)) : sum I M ((DirectSum.lof (AdicCompletion I R) ι (fun i => AdicComp
letion I (M …
· 使用定理 `AdicCompletion.component_sumInv`：component_sumInv (x : AdicCompletion I 
(⨁ j, M j)) (j : ι) : component (AdicCompletion I R) ι _ j (sumInv I M x) = map 
I (component R ι _ j)…
· 使用定理 `AdicCompletion.mk_apply_coe`：∀ {R : Type u_1} [inst : CommRing R] (I : I
deal R) (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   
(f : AdicCompleti…
· 使用定理 `AdicCompletion.AdicCauchySequence.map_apply_coe`：∀ {R : Type u_1} [inst 
: CommRing R] (I : Ideal R) {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _
root_.Module R M]   {N : Type u_3} [i…
· 使用定理 `DirectSum.component.of`：∀ (R : Type u) [inst : Semiring R] {ι : Type v} 
{M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → 
_root_.Modul…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem sumInv_comp_sum : sumInv I M ∘ₗ sum I M = LinearMap.id := by
  ext j x : 2
  apply DirectSum.ext_component (AdicCompletion I R) (fun i ↦ ?_)
  ext n
  simp only [LinearMap.coe_comp, Function.comp_apply, sum_lof, map_mk, component_sumInv,
    mk_apply_coe, AdicCauchySequence.map_apply_coe, Submodule.mkQ_apply, LinearMap.id_comp]
  rw [DirectSum.component.of, DirectSum.component.of]
  split
  · next h => subst h; simp
  · simp
/-
**AdicCompletion.sum_comp_sumInv** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：sum_comp_sumInv : sum I M ∘ₗ sumInv I M = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AdicCompletion.map_ext'`：map_ext' {f g : AdicCompletion I M ->ₗ[AdicComp
letion I R] T} (h : forall (a : AdicCauchySequence I M), f (AdicCompletion.mk I 
M a) = g (Adi…
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdicCompletion.mk_apply_coe`：∀ {R : Type u_1} [inst : CommRing R] (I : I
deal R) (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   
(f : AdicCompleti…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.sum_univ_of`：sum_univ_of [Fintype ι] (x : ⨁ i, β i) : ∑ i in F
inset.univ, of β i (x i) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AdicCompletion.sumInv_apply`：sumInv_apply (x : AdicCompletion I (⨁ j, M 
j)) (j : ι) : (sumInv I M x) j = map I (component R ι _ j) x
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
· 使用定理 `AdicCompletion.sum_of`：sum_of [DecidableEq ι] (j : ι) (x : AdicCompletio
n I (M j)) : sum I M ((DirectSum.of (fun i => AdicCompletion I (M i)) j) x) = ma
p I (lof R …
· 使用引理 `AdicCompletion.val_sum_apply`：val_sum_apply {ι : Type*} (s : Finset ι) (
f : ι -> AdicCompletion I M) (n : Nat) : (∑ i in s, f i).val n = ∑ i in s, (f i)
.val n
· 使用定理 `AdicCompletion.AdicCauchySequence.map_apply_coe`：∀ {R : Type u_1} [inst 
: CommRing R] (I : Ideal R) {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _
root_.Module R M]   {N : Type u_3} [i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_comp_sumInv : sum I M ∘ₗ sumInv I M = LinearMap.id := by
  ext f n
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, mk_apply_coe,
    Submodule.mkQ_apply]
  rw [← DirectSum.sum_univ_of (((sumInv I M) ((AdicCompletion.mk I (⨁ (j : ι), M j)) f)))]
  simp only [sumInv_apply, map_mk, map_sum, sum_of, val_sum_apply, mk_apply_coe,
    AdicCauchySequence.map_apply_coe]
  simp only [← Submodule.mkQ_apply, ← map_sum, ← apply_eq_component, lof_eq_of,
    DirectSum.sum_univ_of]

/-- If `ι` is finite, `sum` has `sumInv` as inverse. -/
/-
**AdicCompletion.sumEquivOfFintype** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：sumEquivOfFintype : (⨁ j, (AdicCompletion I (M j))) ≃ₗ[AdicCompletion I R]
 AdicCompletion I (⨁ j, M j)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AdicCompletion.sum_comp_sumInv`：sum_comp_sumInv : sum I M ∘ₗ sumInv I M 
= LinearMap.id
· 使用定理 `AdicCompletion.sumInv_comp_sum`：sumInv_comp_sum : sumInv I M ∘ₗ sum I M 
= LinearMap.id

--- 原说明 ---
If `ι` is finite, `sum` has `sumInv` as inverse.
-/
def sumEquivOfFintype :
    (⨁ j, (AdicCompletion I (M j))) ≃ₗ[AdicCompletion I R] AdicCompletion I (⨁ j, M j) :=
  LinearEquiv.ofLinearMap (sum I M) (sumInv I M) (sum_comp_sumInv I M) (sumInv_comp_sum I M)

@[simp]
/-
**AdicCompletion.sumEquivOfFintype_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompleti
on`。
形式化陈述：sumEquivOfFintype_apply (x : ⨁ j, (AdicCompletion I (M j))) : sumEquivOfFi
ntype I M x = sum I M x
参数：x : ⨁ j, (AdicCompletion I (M j))。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumEquivOfFintype_apply (x : ⨁ j, (AdicCompletion I (M j))) :
    sumEquivOfFintype I M x = sum I M x :=
  rfl

@[simp]
/-
**AdicCompletion.sumEquivOfFintype_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCom
pletion`。
形式化陈述：sumEquivOfFintype_symm_apply (x : AdicCompletion I (⨁ j, M j)) : (sumEquiv
OfFintype I M).symm x = sumInv I M x
参数：x : AdicCompletion I (⨁ j, M j)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumEquivOfFintype_symm_apply (x : AdicCompletion I (⨁ j, M j)) :
    (sumEquivOfFintype I M).symm x = sumInv I M x :=
  rfl

end Sum

section Pi

open DirectSum

variable [DecidableEq ι] [Fintype ι]

/-- If `ι` is finite, `pi` is a linear equiv. -/
/-
**AdicCompletion.piEquivOfFintype** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：piEquivOfFintype : AdicCompletion I (forall j, M j) ≃ₗ[AdicCompletion I R]
 forall j, AdicCompletion I (M j)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ι` is finite, `pi` is a linear equiv.
-/
def piEquivOfFintype :
    AdicCompletion I (∀ j, M j) ≃ₗ[AdicCompletion I R] ∀ j, AdicCompletion I (M j) :=
  letI f := (congr I (linearEquivFunOnFintype R ι M)).symm
  letI g := (linearEquivFunOnFintype (AdicCompletion I R) ι (fun j ↦ AdicCompletion I (M j)))
  f.trans ((sumEquivOfFintype I M).symm.trans g)

@[simp]
/-
**AdicCompletion.piEquivOfFintype_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletio
n`。
形式化陈述：piEquivOfFintype_apply (x : AdicCompletion I (forall j, M j)) : piEquivOfF
intype I M x = pi I M x
参数：x : AdicCompletion I (forall j, M j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdicCompletion.map_comp_apply`：map_comp_apply (f : M ->ₗ[R] N) (g : N ->
ₗ[R] P) (x : AdicCompletion I M) : map I g (map I f x) = map I (g ∘ₗ f) x
· 使用定理 `LinearEquiv.symm_trans_self`：symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.sy
mm.trans f = LinearEquiv.refl R₂ M₂
· 使用定理 `AdicCompletion.map_id`：map_id : map I (LinearMap.id (M
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piEquivOfFintype_apply (x : AdicCompletion I (∀ j, M j)) :
    piEquivOfFintype I M x = pi I M x := by
  simp [piEquivOfFintype, sumInv, map_comp_apply]

/-- Adic completion of `R^n` is `(AdicCompletion I R)^n`. -/
/-
**AdicCompletion.piEquivFin** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：piEquivFin (n : Nat) : AdicCompletion I (Fin n -> R) ≃ₗ[AdicCompletion I R
] Fin n -> AdicCompletion I R
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adic completion of `R^n` is `(AdicCompletion I R)^n`.
-/
def piEquivFin (n : ℕ) :
    AdicCompletion I (Fin n → R) ≃ₗ[AdicCompletion I R] Fin n → AdicCompletion I R :=
  piEquivOfFintype I (ι := Fin n) (fun _ : Fin n ↦ R)

/-
import Mathlib.RingTheory.AdicCompletion.Algebra

variable {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*) [Fintype ι] [DecidableEq ι]

-- `AdicCompletion.module` has type `Module X Y → Module (F X) (F Y)` so introduces
-- diamonds if `X = Y`.
example : AdicCompletion.module I = Semiring.toModule := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example : ((AdicCompletion.module I).toSMul : SMul (AdicCompletion I R) (AdicCompletion I R)) =
    Semiring.toModule.toSMul := by
  fail_if_success with_reducible_and_instances rfl
  rfl
-/
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AdicCompletion.piEquivFin_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：piEquivFin_apply (n : Nat) (x : AdicCompletion I (Fin n -> R)) : piEquivFi
n I n x = pi I (fun _ : Fin n => R) x
参数：n : Nat；x : AdicCompletion I (Fin n -> R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdicCompletion.piEquivOfFintype_apply`：piEquivOfFintype_apply (x : AdicC
ompletion I (forall j, M j)) : piEquivOfFintype I M x = pi I M x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
import Mathlib.RingTheory.AdicCompletion.Algebra

variable {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*) [Fintype ι] [Decidab
leEq ι]

-- `AdicCompletion.module` has type `Module X Y → Module (F X) (F Y)` so introdu
ces
-- diamonds if `X = Y`.
example : AdicCompletion.module I = Semiring.toModule := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example : ((AdicCompletion.module I).toSMul : SMul (AdicCompletion I R) (AdicCom
pletion I R)) =
    Semiring.toModule.toSMul := by
  fail_if_success with_reducible_and_instances rfl
  rfl
-/
theorem piEquivFin_apply (n : ℕ) (x : AdicCompletion I (Fin n → R)) :
    piEquivFin I n x = pi I (fun _ : Fin n ↦ R) x := by
  simp only [piEquivFin, piEquivOfFintype_apply]

end Pi

end Families

open Submodule

variable {I}

set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.exists_smodEq_pow_add_one_smul** 是 Mathlib 中的一个定理，位于命名空间 `AdicC
ompletion`。
形式化陈述：exists_smodEq_pow_add_one_smul {f : M ->ₗ[R] N} (h : Function.Surjective (
mkQ (I • ⊤) ∘ₗ f)) {y : N} {n : Nat} (hy : y in (I ^ n • ⊤ : Submodule R N)) : e
xists x in (I ^ n • ⊤ : Submodule R M), f x ≡ y [SMOD (I ^ (n + 1) • ⊤ : Submodu
le R N)]
参数：h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)；hy : y in (I ^ n • ⊤ : Submodule R
 N)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.smul_induction_on'`：smul_induction_on' {x : M} (hx : x in I • 
N) {p : forall x, x in I • N -> Prop} (smul : forall (r : A) (hr : r in I) (n : 
M) (hn : n in N), …
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `SModEq.smul'`：smul' (hxy : x ≡ y [SMOD U]) {c : R} (hc : c in I) : c • x
 ≡ c • y [SMOD (I • U)]
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SModEq.add`：add (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁
 + x₂ ≡ y₁ + y₂ [SMOD U]
-/
theorem exists_smodEq_pow_add_one_smul {f : M →ₗ[R] N}
    (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) {y : N} {n : ℕ}
    (hy : y ∈ (I ^ n • ⊤ : Submodule R N)) :
    ∃ x ∈ (I ^ n • ⊤ : Submodule R M), f x ≡ y [SMOD (I ^ (n + 1) • ⊤ : Submodule R N)] := by
  induction hy using smul_induction_on' with
  | smul r hr y _ =>
    obtain ⟨x, hx⟩ := h (mkQ _ y)
    use r • x, smul_mem_smul hr mem_top
    simp only [coe_comp, Function.comp_apply, mkQ_apply, ← SModEq.def, map_smul] at ⊢ hx
    rw [pow_succ, ← smul_smul]
    exact SModEq.smul' hx hr
  | add y1 hy1 y2 hy2 ih1 ih2 =>
    obtain ⟨x1, hx1, hx1'⟩ := ih1
    obtain ⟨x2, hx2, hx2'⟩ := ih2
    use x1 + x2, add_mem hx1 hx2
    simp only [map_add]
    exact SModEq.add hx1' hx2'
/-
**AdicCompletion.exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_top** 是 
Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_top {f : M ->ₗ[R] N
} (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) {x : M} {y : N} {n : Nat} (hxy : 
f x ≡ y [SMOD (I ^ n • ⊤ : Submodule R N)]) : exists x' : M, x ≡ x' [SMOD (I ^ n
 • ⊤ : Submodule R M)] ∧ f x' ≡ y [SMOD (I ^ (n + 1) • ⊤ : Submodule R N)]
参数：h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)；hxy : f x ≡ y [SMOD (I ^ n • ⊤ : S
ubmodule R N)]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AdicCompletion.exists_smodEq_pow_add_one_smul`：exists_smodEq_pow_add_one
_smul {f : M ->ₗ[R] N} (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) {y : N} {n :
 Nat} (hy : y in (I ^ n • ⊤ : Submo…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SModEq.sub_mem`：sub_mem : x ≡ y [SMOD U] ↔ x - y in U
· 使用定理 `SModEq.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡
 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - (a + b) = -b
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `sub_sub_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b c
 : α), a - (b - c) = a + c - b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_top {f : M →ₗ[R] N}
    (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) {x : M} {y : N} {n : ℕ}
    (hxy : f x ≡ y [SMOD (I ^ n • ⊤ : Submodule R N)]) :
    ∃ x' : M, x ≡ x' [SMOD (I ^ n • ⊤ : Submodule R M)] ∧
    f x' ≡ y [SMOD (I ^ (n + 1) • ⊤ : Submodule R N)] := by
  obtain ⟨z, hz, hz'⟩ :=
    exists_smodEq_pow_add_one_smul h (y := y - f x) (SModEq.sub_mem.mp hxy.symm)
  use x + z
  constructor
  · simpa [SModEq.sub_mem]
  · simpa [SModEq.sub_mem, sub_sub_eq_add_sub, add_comm] using hz'
/-
**AdicCompletion.exists_smodEq_pow_smul_top_and_mkQ_eq** 是 Mathlib 中的一个定理，位于命名空间
 `AdicCompletion`。
形式化陈述：exists_smodEq_pow_smul_top_and_mkQ_eq {f : M ->ₗ[R] N} (h : Function.Surje
ctive (mkQ (I • ⊤) ∘ₗ f)) {x : M} {n : Nat} {y : N ⧸ (I ^ n • ⊤ : Submodule R N)
} {y' : N ⧸ (I ^ (n + 1) • ⊤ : Submodule R N)} (hyy' : factor (pow_smul_top_le I
 N n.le_succ) y' = y) (hxy : mkQ _ (f x) = y) : exists x' : M, x ≡ x' [SMOD (I ^
 n • ⊤ : Submodule R M)] ∧ mkQ _ (f x') = y'
参数：h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)；I ^ n • ⊤ : Submodule R N；I ^ (n +
 1) • ⊤ : Submodule R N；hyy' : factor (pow_smul_top_le I N n.le_succ) y' = y；hxy
 : mkQ _ (f x) = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Submodule.pow_smul_top_le`：pow_smul_top_le {m n : Nat} (h : m <= n) : (I
 ^ n • ⊤ : Submodule R M) <= I ^ m • ⊤
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SModEq.eq_1`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   (U : Submodule R M) (x y : M), (x 
≡…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `Submodule.factor_mk`：factor_mk (H : p <= p') (x : M) : factor H (mkQ p x
) = mkQ p' x
· 使用定理 `AdicCompletion.exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_to
p`：exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_top {f : M ->ₗ[R] N} (
h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) {x : M} {y : N} {n …
-/
theorem exists_smodEq_pow_smul_top_and_mkQ_eq {f : M →ₗ[R] N}
    (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) {x : M} {n : ℕ}
    {y : N ⧸ (I ^ n • ⊤ : Submodule R N)} {y' : N ⧸ (I ^ (n + 1) • ⊤ : Submodule R N)}
    (hyy' : factor (pow_smul_top_le I N n.le_succ) y' = y) (hxy : mkQ _ (f x) = y) :
    ∃ x' : M, x ≡ x' [SMOD (I ^ n • ⊤ : Submodule R M)] ∧ mkQ _ (f x') = y' := by
  obtain ⟨y0, hy0⟩ := mkQ_surjective _ y'
  have : f x ≡ y0 [SMOD (I ^ n • ⊤ : Submodule R N)] := by
    rw [SModEq, ← mkQ_apply, ← mkQ_apply, ← factor_mk (pow_smul_top_le I N n.le_succ) y0,
        hy0, hyy', hxy]
  obtain ⟨x', hxx', hx'y0⟩ :=
    exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_top h this
  use x', hxx'
  rwa [mkQ_apply, hx'y0]

set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.map_surjective_of_mkQ_comp_surjective** 是 Mathlib 中的一个定理，位于命名空间
 `AdicCompletion`。
形式化陈述：map_surjective_of_mkQ_comp_surjective {f : M ->ₗ[R] N} (h : Function.Surje
ctive (mkQ (I • ⊤) ∘ₗ f)) : Function.Surjective (map I f)
参数：h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Submodule.top_smul`：top_smul : (⊤ : Ideal R) • N = N
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearMap.range_id`：range_id : range (LinearMap.id : M ->ₗ[R] M) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AdicCompletion.exists_smodEq_pow_smul_top_and_mkQ_eq`：exists_smodEq_pow_
smul_top_and_mkQ_eq {f : M ->ₗ[R] N} (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)
) {x : M} {n : Nat} {y : N ⧸ (I ^ n • ⊤ : …
· 使用引理 `Submodule.pow_smul_top_le`：pow_smul_top_le {m n : Nat} (h : m <= n) : (I
 ^ n • ⊤ : Submodule R M) <= I ^ m • ⊤
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `AdicCompletion.transitionMap_comp_eval_apply`：transitionMap_comp_eval_ap
ply {m n : Nat} (hmn : m <= n) (x : AdicCompletion I M) : transitionMap I M hmn 
(x.val n) = x.val m
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Submodule.eq_factor_of_eq_factor_succ`：Submodule.eq_factor_of_eq_factor_
succ {p : Nat -> Submodule R M} (hp : Antitone p) (x : (n : Nat) -> M ⧸ (p n)) (
h : forall m, x m = factor …
（共 33 条，此处仅展示前 30 条）
-/
theorem map_surjective_of_mkQ_comp_surjective {f : M →ₗ[R] N}
    (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) : Function.Surjective (map I f) := by
  intro y
  suffices h : ∃ x : ℕ → M, ∀ n, x n ≡ x (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)] ∧
      Submodule.Quotient.mk (f (x n)) = eval I _ n y by
    obtain ⟨x, hx⟩ := h
    use AdicCompletion.mk I M ⟨x, fun h ↦
        eq_factor_of_eq_factor_succ (fun _ _ ↦ pow_smul_top_le I M) _ (fun n ↦ (hx n).1) h⟩
    ext n
    simp [hx n]
  let x : (n : ℕ) → {m : M // Submodule.Quotient.mk (f m) = eval I _ n y} := fun n ↦ by
    induction n with
    | zero =>
      use 0
      apply_fun (Submodule.Quotient.equiv (I ^ 0 • ⊤) ⊤ (.refl R N) (by simp)).toEquiv
      exact Subsingleton.elim _ _
    | succ n xn =>
      choose z hz using exists_smodEq_pow_smul_top_and_mkQ_eq h
          (y' := eval _ _ (n + 1) y) (by simp) xn.2
      exact ⟨z, hz.2⟩
  exact ⟨fun n ↦ (x n).val, fun n ↦ ⟨(Classical.choose_spec (exists_smodEq_pow_smul_top_and_mkQ_eq
      h (y' := eval I _ (n + 1) y) (by simp) (x n).2)).1, (x n).property⟩⟩

end AdicCompletion

open AdicCompletion Submodule

variable {I}

/-
**surjective_of_mkQ_comp_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjective_of_mkQ_comp_surjective [IsPrecomplete I M] [IsHausdorff I N] {f
 : M ->ₗ[R] N} (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) : Function.Surjectiv
e f
参数：h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AdicCompletion.map_surjective_of_mkQ_comp_surjective`：map_surjective_of_
mkQ_comp_surjective {f : M ->ₗ[R] N} (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)
) : Function.Surjective (map I f)
· 使用定理 `AdicCompletion.of_surjective`：of_surjective [IsPrecomplete I M] : Functi
on.Surjective (of I M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AdicCompletion.of_inj`：of_inj [IsHausdorff I M] {a b : M} : of I M a = o
f I M b ↔ a = b
· 使用定理 `AdicCompletion.map_of`：map_of (f : M ->ₗ[R] N) (x : M) : map I f (of I M
 x) = of I N (f x)
-/
theorem surjective_of_mkQ_comp_surjective [IsPrecomplete I M] [IsHausdorff I N]
    {f : M →ₗ[R] N} (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) : Function.Surjective f := by
  intro y
  obtain ⟨x', hx'⟩ := AdicCompletion.map_surjective_of_mkQ_comp_surjective h (of I N y)
  obtain ⟨x, hx⟩ := of_surjective I M x'
  use x
  rwa [← of_inj (I := I), ← map_of, hx]

variable {S : Type*} [CommRing S] (f : R →+* S)
/-
**surjective_of_mk_map_comp_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjective_of_mk_map_comp_surjective [IsPrecomplete I R] [haus : IsHausdor
ff (I.map f) S] (h : Function.Surjective ((Ideal.Quotient.mk (I.map f)).comp f))
 : Function.Surjective f
参数：I.map f；h : Function.Surjective ((Ideal.Quotient.mk (I.map f)).comp f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.smul_top_eq_map`：smul_top_eq_map {R S : Type*} [CommSemiring R] [C
ommSemiring S] [Algebra R S] (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (a
lgebraMap R…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsHausdorff.map_algebraMap_iff`：IsHausdorff.map_algebraMap_iff [CommRing
 S] [Module S M] [Algebra R S] [IsScalarTower R S M] : IsHausdorff (I.map (algeb
raMap R S)) M ↔ IsHa…
· 使用定理 `surjective_of_mkQ_comp_surjective`：surjective_of_mkQ_comp_surjective [Is
Precomplete I M] [IsHausdorff I N] {f : M ->ₗ[R] N} (h : Function.Surjective (mk
Q (I • ⊤) ∘ₗ f)) : Func…
-/
theorem surjective_of_mk_map_comp_surjective [IsPrecomplete I R] [haus : IsHausdorff (I.map f) S]
    (h : Function.Surjective ((Ideal.Quotient.mk (I.map f)).comp f)) :
    Function.Surjective f := by
  let _ := f.toAlgebra
  let fₗ := (Algebra.ofId R S).toLinearMap
  change Function.Surjective ((restrictScalars R (I.map f)).mkQ ∘ₗ fₗ) at h
  have : I • ⊤ = restrictScalars R (Ideal.map f I) := by
    simp only [Ideal.smul_top_eq_map, restrictScalars_inj]
    rfl
  have _ := IsHausdorff.map_algebraMap_iff.mp haus
  apply surjective_of_mkQ_comp_surjective (I := I) (f := fₗ)
  rwa [Ideal.smul_top_eq_map]
