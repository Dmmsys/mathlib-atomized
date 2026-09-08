/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Algebra instance on adic completion

In this file we provide an algebra instance on the adic completion of a ring. Then the adic
completion of any module is a module over the adic completion of the ring.

## Main definitions

- `evalₐ`: the canonical algebra map from the adic completion to `R ⧸ I ^ n`.

- `AdicCompletion.liftRingHom`: given a compatible family of ring maps
  `R →+* S ⧸ I ^ n`, the lift ring map `R →+* AdicCompletion I S`.

## Implementation details

We do not make a separate adic completion type in algebra case, to not duplicate all
module-theoretic results on adic completions. This choice does cause some trouble though,
since `I ^ n • ⊤` is not defeq to `I ^ n`. We try to work around most of the trouble by
providing as much API as possible.

-/

@[expose] public section

suppress_compilation

open Submodule

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]

namespace AdicCompletion

attribute [-simp] smul_eq_mul

@[local simp]
/-
**AdicCompletion.transitionMap_ideal_mk** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletio
n`。
形式化陈述：transitionMap_ideal_mk {m n : Nat} (hmn : m <= n) (x : R) : transitionMap 
I R hmn (Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) x) = Ideal.Quotient.mk (I ^ m •
 ⊤ : Ideal R) x
参数：hmn : m <= n；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem transitionMap_ideal_mk {m n : ℕ} (hmn : m ≤ n) (x : R) :
    transitionMap I R hmn (Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) x) =
      Ideal.Quotient.mk (I ^ m • ⊤ : Ideal R) x :=
  rfl

@[local simp]
/-
**AdicCompletion.transitionMap_map_one** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion
`。
形式化陈述：transitionMap_map_one {m n : Nat} (hmn : m <= n) : transitionMap I R hmn 1
 = 1
参数：hmn : m <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transitionMap_map_one {m n : ℕ} (hmn : m ≤ n) : transitionMap I R hmn 1 = 1 :=
  rfl

@[local simp]
/-
**AdicCompletion.transitionMap_map_mul** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion
`。
形式化陈述：transitionMap_map_mul {m n : Nat} (hmn : m <= n) (x y : R ⧸ (I ^ n • ⊤ : I
deal R)) : transitionMap I R hmn (x * y) = transitionMap I R hmn x * transitionM
ap I R hmn y
参数：hmn : m <= n；x y : R ⧸ (I ^ n • ⊤ : Ideal R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Quotient.inductionOn₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} 
{s₂ : Setoid β} {p : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q₂ 
: Quotient s…
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem transitionMap_map_mul {m n : ℕ} (hmn : m ≤ n) (x y : R ⧸ (I ^ n • ⊤ : Ideal R)) :
    transitionMap I R hmn (x * y) = transitionMap I R hmn x * transitionMap I R hmn y :=
  Quotient.inductionOn₂' x y (fun _ _ ↦ rfl)

@[local simp]
/-
**AdicCompletion.transitionMap_map_pow** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion
`。
形式化陈述：transitionMap_map_pow {m n a : Nat} (hmn : m <= n) (x : R ⧸ (I ^ n • ⊤ : I
deal R)) : transitionMap I R hmn (x ^ a) = transitionMap I R hmn x ^ a
参数：hmn : m <= n；x : R ⧸ (I ^ n • ⊤ : Ideal R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem transitionMap_map_pow {m n a : ℕ} (hmn : m ≤ n) (x : R ⧸ (I ^ n • ⊤ : Ideal R)) :
    transitionMap I R hmn (x ^ a) = transitionMap I R hmn x ^ a :=
  Quotient.inductionOn' x (fun _ ↦ rfl)

/-- `AdicCompletion.transitionMap` as an algebra homomorphism. -/
/-
**AdicCompletion.transitionMap** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AdicCompletion.transitionMap {m n : Nat} (hmn : m <= n)
参数：hmn : m <= n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AdicCompletion.transitionMap` as an algebra homomorphism.
-/
def transitionMapₐ {m n : ℕ} (hmn : m ≤ n) :
    R ⧸ (I ^ n • ⊤ : Ideal R) →ₐ[R] R ⧸ (I ^ m • ⊤ : Ideal R) :=
  AlgHom.ofLinearMap (transitionMap I R hmn) rfl (transitionMap_map_mul I hmn)

/-- `AdicCompletion I R` is an `R`-subalgebra of `∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)`. -/
/-
**AdicCompletion.subalgebra** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：subalgebra : Subalgebra R (forall n, R ⧸ (I ^ n • ⊤ : Ideal R))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AdicCompletion I R` is an `R`-subalgebra of `∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)`.
-/
def subalgebra : Subalgebra R (∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)) :=
  Submodule.toSubalgebra (submodule I R) (fun _ ↦ by simp [transitionMap_map_one I])
    (fun x y hx hy m n hmn ↦ by simp [hx hmn, hy hmn, transitionMap_map_mul I hmn])

/-- `AdicCompletion I R` is a subring of `∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)`. -/
/-
**AdicCompletion.subring** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：subring : Subring (forall n, R ⧸ (I ^ n • ⊤ : Ideal R))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AdicCompletion I R` is a subring of `∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)`.
-/
def subring : Subring (∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)) :=
  Subalgebra.toSubring (subalgebra I)
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (AdicCompletion I R) where
  mul x y := ⟨x.val * y.val, fun hmn ↦ by
    simp [x.property, y.property, transitionMap_map_mul I hmn]⟩
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (AdicCompletion I R) where
  one := ⟨1, by simp [transitionMap_map_one I]⟩
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (AdicCompletion I R) where
  natCast n := ⟨n, fun _ ↦ rfl⟩
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IntCast (AdicCompletion I R) where
  intCast n := ⟨n, fun _ ↦ rfl⟩
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (AdicCompletion I R) ℕ where
  pow x n := ⟨x.val ^ n, fun hmn ↦ by simp [x.property, transitionMap_map_pow I hmn]⟩
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing (AdicCompletion I R) :=
  let f : AdicCompletion I R → ∀ n, R ⧸ (I ^ n • ⊤ : Ideal R) := Subtype.val
  Subtype.val_injective.commRing f rfl rfl
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra S R] : Algebra S (AdicCompletion I R) where
  algebraMap :=
  { toFun r := ⟨algebraMap S (∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)) r, fun hmn ↦ by
      simp only [Pi.algebraMap_apply,
        IsScalarTower.algebraMap_apply S R (R ⧸ (I ^ _ • ⊤ : Ideal R)),
        Ideal.Quotient.algebraMap_eq, mapQ_eq_factor]
      rfl⟩
    map_one' := Subtype.ext <| map_one _
    map_mul' x y := Subtype.ext <| map_mul _ x y
    map_zero' := Subtype.ext <| map_zero _
    map_add' x y := Subtype.ext <| map_add _ x y }
  commutes' r x := Subtype.ext <| Algebra.commutes' r x.val
  smul_def' r x := Subtype.ext <| Algebra.smul_def' r x.val
/-
**AdicCompletion.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：algebraMap_apply [Algebra S R] (s : S) : algebraMap S (AdicCompletion I R)
 s = of I R (algebraMap S R s)
参数：s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply [Algebra S R] (s : S) :
    algebraMap S (AdicCompletion I R) s = of I R (algebraMap S R s) := rfl

@[simp]
/-
**AdicCompletion.val_one** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：val_one (n : Nat) : (1 : AdicCompletion I R).val n = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_one (n : ℕ) : (1 : AdicCompletion I R).val n = 1 :=
  rfl

@[simp]
/-
**AdicCompletion.val_mul** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：val_mul (n : Nat) (x y : AdicCompletion I R) : (x * y).val n = x.val n * y
.val n
参数：n : Nat；x y : AdicCompletion I R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_mul (n : ℕ) (x y : AdicCompletion I R) : (x * y).val n = x.val n * y.val n :=
  rfl

/-- The canonical algebra map from the adic completion to `R ⧸ I ^ n`.

This is `AdicCompletion.eval` postcomposed with the algebra isomorphism
`R ⧸ (I ^ n • ⊤) ≃ₐ[R] R ⧸ I ^ n`. -/
/-
**AdicCompletion.eval** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：eval (n : Nat) : AdicCompletion I M ->ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M)
 where toFun f
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical algebra map from the adic completion to `R ⧸ I ^ n`.

This is `AdicCompletion.eval` postcomposed with the algebra isomorphism
`R ⧸ (I ^ n • ⊤) ≃ₐ[R] R ⧸ I ^ n`.
-/
def evalₐ (n : ℕ) : AdicCompletion I R →ₐ[R] R ⧸ I ^ n :=
  have h : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  AlgHom.comp
    (Ideal.quotientEquivAlgOfEq R h)
    (AlgHom.ofLinearMap (eval I R n) rfl (fun _ _ ↦ rfl))

set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.factor_eval** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factor_evalₐ_eq_eval {n : ℕ} (x : AdicCompletion I R) (h : I ^ n ≤ I ^ n • ⊤) :
    Ideal.Quotient.factor h (evalₐ I n x) = eval I R n x := by
  simp [evalₐ]

set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.factor_eval_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factor_eval_eq_evalₐ {n : ℕ} (x : AdicCompletion I R) (h : I ^ n • ⊤ ≤ I ^ n) :
    factor h (eval I R n x) = evalₐ I n x := by
  simp [evalₐ]

set_option backward.isDefEq.respectTransparency false in
/--
The composition map `R →+* AdicCompletion I R →+* R ⧸ I ^ n` equals to the natural quotient map.
-/
@[simp]
/-
**AdicCompletion.eval** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：eval (n : Nat) : AdicCompletion I M ->ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M)
 where toFun f
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition map `R →+* AdicCompletion I R →+* R ⧸ I ^ n` equals to the natur
al quotient map.
-/
theorem evalₐ_of (n : ℕ) (x : R) :
    evalₐ I n (of I R x) = Ideal.Quotient.mk _ x := by
  simp [evalₐ]
/-
**AdicCompletion.surjective_eval** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem surjective_evalₐ (n : ℕ) : Function.Surjective (evalₐ I n) := by
  simp only [evalₐ, smul_eq_mul, Ideal.quotientEquivAlgOfEq_coe_eq_factorₐ,
    AlgHom.coe_comp]
  apply Function.Surjective.comp
  · exact factor_surjective Ideal.mul_le_left
  · exact eval_surjective I R n

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AdicCompletion.eval** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：eval (n : Nat) : AdicCompletion I M ->ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M)
 where toFun f
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evalₐ_mk (n : ℕ) (x : AdicCauchySequence I R) :
    evalₐ I n (mk I R x) = Ideal.Quotient.mk (I ^ n) (x.val n) := by
  simp [evalₐ]

variable {I} in
/-
**AdicCompletion.ext_eval** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ext_evalₐ {x y : AdicCompletion I R} (H : ∀ n, evalₐ I n x = evalₐ I n y) : x = y := by
  ext n
  have h : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  exact (Ideal.quotientEquivAlgOfEq R h).injective (H n)

/-- The canonical projection from the `I`-adic completion to `R ⧸ I`. -/
/-
**AdicCompletion.evalOne** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection from the `I`-adic completion to `R ⧸ I`.
-/
def evalOneₐ : AdicCompletion I R →ₐ[R] R ⧸ I :=
  (Ideal.Quotient.factorₐ _ (by simp)).comp (evalₐ _ 1)

@[simp]
/-
**AdicCompletion.evalOne** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma evalOneₐ_of (x : R) : evalOneₐ I (of I R x) = x := rfl

@[simp]
/-
**AdicCompletion.factor** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma factorₐ_evalₐ_one (x : AdicCompletion I R) :
    Ideal.Quotient.factor (show I ^ 1 ≤ I by simp) (evalₐ I 1 x) = evalOneₐ I x :=
  rfl
/-
**AdicCompletion.evalOne** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma evalOneₐ_comp_algebraMap_eq_mk :
    (AdicCompletion.evalOneₐ I).toRingHom.comp (algebraMap R (AdicCompletion I R)) =
      (Ideal.Quotient.mk I) :=
  rfl
/-
**AdicCompletion.evalOne** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma evalOneₐ_surjective : Function.Surjective (evalOneₐ I) := by
  dsimp [evalOneₐ]
  exact (Ideal.Quotient.factor_surjective (show I ^ 1 ≤ I by simp)).comp
    (AdicCompletion.surjective_evalₐ I 1)

/-- `AdicCauchySequence I R` is an `R`-subalgebra of `ℕ → R`. -/
/-
**AdicCompletion.AdicCauchySequence.subalgebra** 是 Mathlib 中的一个定义，位于命名空间 `AdicCo
mpletion.AdicCauchySequence`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → Ideal R → Subalgebra R (ℕ → R)
参数：ℕ → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AdicCauchySequence I R` is an `R`-subalgebra of `ℕ → R`.
-/
def AdicCauchySequence.subalgebra : Subalgebra R (ℕ → R) :=
  Submodule.toSubalgebra (AdicCauchySequence.submodule I R)
    (fun {m n} _ ↦ by simp)
    (fun x y hx hy {m n} hmn ↦ by
      simp only [Pi.mul_apply]
      exact SModEq.mul (hx hmn) (hy hmn))

/-- `AdicCauchySequence I R` is a subring of `ℕ → R`. -/
/-
**AdicCompletion.AdicCauchySequence.subring** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompl
etion.AdicCauchySequence`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → Ideal R → Subring (ℕ → R)
参数：ℕ → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AdicCauchySequence I R` is a subring of `ℕ → R`.
-/
def AdicCauchySequence.subring : Subring (ℕ → R) :=
  Subalgebra.toSubring (AdicCauchySequence.subalgebra I)
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (AdicCauchySequence I R) where
  mul x y := ⟨x.val * y.val, fun hmn ↦ SModEq.mul (x.property hmn) (y.property hmn)⟩
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (AdicCauchySequence I R) where
  one := ⟨1, fun _ ↦ rfl⟩
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (AdicCauchySequence I R) where
  natCast n := ⟨n, fun _ ↦ rfl⟩
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IntCast (AdicCauchySequence I R) where
  intCast n := ⟨n, fun _ ↦ rfl⟩
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (AdicCauchySequence I R) ℕ where
  pow x n := ⟨x.val ^ n, fun hmn ↦ SModEq.pow n (x.property hmn)⟩
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing (AdicCauchySequence I R) :=
  let f : AdicCauchySequence I R → (ℕ → R) := Subtype.val
  Subtype.val_injective.commRing f rfl rfl
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra R (AdicCauchySequence I R) where
  algebraMap :=
  { toFun r := ⟨algebraMap R (∀ _, R) r, fun _ ↦ rfl⟩
    map_one' := Subtype.ext <| map_one _
    map_mul' x y := Subtype.ext <| map_mul _ x y
    map_zero' := Subtype.ext <| map_zero _
    map_add' x y := Subtype.ext <| map_add _ x y }
  commutes' r x := Subtype.ext <| Algebra.commutes' r x.val
  smul_def' r x := Subtype.ext <| Algebra.smul_def' r x.val

@[simp]
/-
**AdicCompletion.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：one_apply (n : Nat) : (1 : AdicCauchySequence I R) n = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (n : ℕ) : (1 : AdicCauchySequence I R) n = 1 :=
  rfl

@[simp]
/-
**AdicCompletion.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：mul_apply (n : Nat) (f g : AdicCauchySequence I R) : (f * g) n = f n * g n
参数：n : Nat；f g : AdicCauchySequence I R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (n : ℕ) (f g : AdicCauchySequence I R) : (f * g) n = f n * g n :=
  rfl

/-- The canonical algebra map from adic Cauchy sequences to the adic completion. -/
@[simps!]
/-
**AdicCompletion.mk** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：mk : AdicCauchySequence I M ->ₗ[R] AdicCompletion I M where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical algebra map from adic Cauchy sequences to the adic completion.
-/
def mkₐ : AdicCauchySequence I R →ₐ[R] AdicCompletion I R :=
  AlgHom.ofLinearMap (mk I R) rfl (fun _ _ ↦ rfl)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AdicCompletion.eval** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：eval (n : Nat) : AdicCompletion I M ->ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M)
 where toFun f
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evalₐ_mkₐ (n : ℕ) (x : AdicCauchySequence I R) :
    evalₐ I n (mkₐ I x) = Ideal.Quotient.mk (I ^ n) (x.val n) := by
  simp [mkₐ]
/-
**AdicCompletion.Ideal.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion.Ideal`
。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) {m n : ℕ},   m ≤ n →   
  ∀ (r : AdicCompletion.AdicCauchySequence I R),       (Ideal.Quotient.mk (I ^ m
)) (↑r n) = (Ideal.Quotient.mk (I ^ m)) (↑r m)
参数：I : Ideal R；r : AdicCompletion.AdicCauchySequence I R；Ideal.Quotient.mk (I ^ 
m)；↑r n；Ideal.Quotient.mk (I ^ m)；↑r m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.smul_top_eq_map`：smul_top_eq_map {R S : Type*} [CommSemiring R] [C
ommSemiring S] [Algebra R S] (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (a
lgebraMap R…
· 使用定理 `Submodule.restrictScalars.congr_simp`：∀ (S : Type u_1) {R : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S
]   [inst_3 : _root_.Modul…
· 使用定理 `Ideal.map_id`：map_id : I.map (RingHom.id R) = I
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Quotient.mk_eq_mk`：mk_eq_mk (x : R) : (Submodule.Quotient.mk x : R
 ⧸ I) = mk I x
· 使用定理 `SModEq.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡
 …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Ideal.mk_eq_mk {m n : ℕ} (hmn : m ≤ n) (r : AdicCauchySequence I R) :
    Ideal.Quotient.mk (I ^ m) (r.val n) = Ideal.Quotient.mk (I ^ m) (r.val m) := by
  have h : I ^ m = I ^ m • ⊤ := by simp
  rw [← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk, h]
  exact (r.property hmn).symm
/-
**AdicCompletion.smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：smul_mk {m n : Nat} (hmn : m <= n) (r : AdicCauchySequence I R) (x : AdicC
auchySequence I M) : r.val n • Submodule.Quotient.mk (p
参数：hmn : m <= n；r : AdicCauchySequence I R；x : AdicCauchySequence I M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.Quotient.mk_smul`：mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ 
p) = r • mk x
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Module.Quotient.mk_smul_mk`：∀ {R : Type u_1} (M : Type u_2) [inst : Ring
 R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (I : Ideal R)   [inst
_3 : I.IsTwoSide…
· 使用定理 `AdicCompletion.AdicCauchySequence.mk_eq_mk`：mk_eq_mk {m n : Nat} (hmn : 
m <= n) (f : AdicCauchySequence I M) : Submodule.Quotient.mk (p
· 使用定理 `AdicCompletion.Ideal.mk_eq_mk`：∀ {R : Type u_1} [inst : CommRing R] (I :
 Ideal R) {m n : ℕ},   m ≤ n →     ∀ (r : AdicCompletion.AdicCauchySequence I R)
,       (Ideal.Quot…
-/
theorem smul_mk {m n : ℕ} (hmn : m ≤ n) (r : AdicCauchySequence I R)
    (x : AdicCauchySequence I M) :
    r.val n • Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (x.val n) =
      r.val m • Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (x.val m) := by
  rw [← Submodule.Quotient.mk_smul, ← Module.Quotient.mk_smul_mk,
    AdicCauchySequence.mk_eq_mk hmn, Ideal.mk_eq_mk I hmn, Module.Quotient.mk_smul_mk,
    Submodule.Quotient.mk_smul]

/-- Scalar multiplication of `R ⧸ (I • ⊤)` on `M ⧸ (I • ⊤)`. This is used in order to have
good definitional behaviour for the module instance on adic completions -/
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication of `R ⧸ (I • ⊤)` on `M ⧸ (I • ⊤)`. This is used in order t
o have
good definitional behaviour for the module instance on adic completions
-/
instance : SMul (R ⧸ (I • ⊤ : Ideal R)) (M ⧸ (I • ⊤ : Submodule R M)) where
  smul r x :=
    Quotient.liftOn r (· • x) fun b₁ b₂ h ↦ by
      induction x using Quotient.inductionOn'
      have h : b₁ - b₂ ∈ (I : Submodule R R) := by
        rwa [show I = I • ⊤ by simp, ← Submodule.quotientRel_def]
      rw [← sub_eq_zero, ← sub_smul, Submodule.Quotient.mk''_eq_mk,
        ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul h mem_top

@[local simp]
/-
**AdicCompletion.mk_smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：mk_smul_mk (r : R) (x : M) : Ideal.Quotient.mk (I • ⊤) r • Submodule.Quoti
ent.mk (p
参数：r : R；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem mk_smul_mk (r : R) (x : M) :
    Ideal.Quotient.mk (I • ⊤) r • Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) x
      = r • Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) x :=
  rfl
/-
**AdicCompletion.val_smul_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_smul_eq_evalₐ_smul (n : ℕ) (r : AdicCompletion I R)
    (x : M ⧸ (I ^ n • ⊤ : Submodule R M)) : r.val n • x = evalₐ I n r • x := by
  induction r using induction_on; rfl
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module (R ⧸ (I • ⊤ : Ideal R)) (M ⧸ (I • ⊤ : Submodule R M)) :=
  Function.Surjective.moduleLeft (Ideal.Quotient.mk (I • ⊤ : Ideal R))
    Ideal.Quotient.mk_surjective (fun _ _ ↦ rfl)
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R (R ⧸ (I • ⊤ : Ideal R)) (M ⧸ (I • ⊤ : Submodule R M)) where
  smul_assoc r s x := by
    induction s, x using Quotient.inductionOn₂' with | _ s x
    simp only [Submodule.Quotient.mk''_eq_mk]
    rw [← Submodule.Quotient.mk_smul, Ideal.Quotient.mk_eq_mk, mk_smul_mk, smul_assoc]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.smul** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
形式化陈述：smul : SMul (AdicCompletion I R) (AdicCompletion I M) where smul r x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smul : SMul (AdicCompletion I R) (AdicCompletion I M) where
  smul r x := {
    val := fun n ↦ eval I R n r • eval I M n x
    property := fun {m n} hmn ↦ by
      apply induction_on I R r (fun r ↦ ?_)
      apply induction_on I M x (fun x ↦ ?_)
      simp only [coe_eval, mapQ_eq_factor, mk_apply_coe, mkQ_apply, Ideal.Quotient.mk_eq_mk,
        mk_smul_mk, map_smul, mapQ_apply, LinearMap.id_coe, id_eq]
      rw [smul_mk I hmn]
  }

@[simp]
/-
**AdicCompletion.smul_eval** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：smul_eval (n : Nat) (r : AdicCompletion I R) (x : AdicCompletion I M) : (r
 • x).val n = r.val n • x.val n
参数：n : Nat；r : AdicCompletion I R；x : AdicCompletion I M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_eval (n : ℕ) (r : AdicCompletion I R) (x : AdicCompletion I M) :
    (r • x).val n = r.val n • x.val n :=
  rfl

/-- `AdicCompletion I M` is naturally an `AdicCompletion I R` module. -/
/-
**AdicCompletion.module** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
形式化陈述：module : Module (AdicCompletion I R) (AdicCompletion I M) where one_smul b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AdicCompletion I M` is naturally an `AdicCompletion I R` module.
-/
instance module : Module (AdicCompletion I R) (AdicCompletion I M) where
  one_smul b := by
    ext n
    simp only [smul_eval, val_one, one_smul]
  mul_smul r s x := by
    ext n
    simp only [smul_eval, val_mul, mul_smul]
  smul_zero r := by ext n; simp
  smul_add r x y := by ext n; simp
  add_smul r s x := by ext n; simp [add_smul]
  zero_smul x := by ext n; simp
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R (AdicCompletion I R) (AdicCompletion I M) where
  smul_assoc r s x := by
    ext n
    rw [smul_eval, val_smul_apply, val_smul_apply, smul_eval, smul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A priori `AdicCompletion I R` has two `AdicCompletion I R`-module instances.
Both agree definitionally. -/
/-
**AdicCompletion.** 是 Mathlib 中的一个示例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A priori `AdicCompletion I R` has two `AdicCompletion I R`-module instances.
Both agree definitionally.
-/
example : module I = @Algebra.toModule (AdicCompletion I R)
    (AdicCompletion I R) _ _ (Algebra.id _) := by
  with_reducible_and_instances rfl

section liftRingHom

open Quotient

variable {R S : Type*} [NonAssocSemiring R] [CommRing S] (I : Ideal S)

set_option backward.isDefEq.respectTransparency false in
/--
The universal property of `AdicCompletion` for rings.
The lift ring map `R →+* AdicCompletion I S` of a compatible family of
ring maps `R →+* S ⧸ I ^ n`.
-/
/-
**AdicCompletion.liftRingHom** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：liftRingHom (f : (n : Nat) -> R ->+* S ⧸ I ^ n) (hf : forall {m n : Nat} (
hle : m <= n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m) : R ->+* AdicC
ompletion I S where toFun
参数：f : (n : Nat) -> R ->+* S ⧸ I ^ n；hf : forall {m n : Nat} (hle : m <= n), (Id
eal.Quotient.factorPow I hle).comp (f n) = f m。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The universal property of `AdicCompletion` for rings.
The lift ring map `R →+* AdicCompletion I S` of a compatible family of
ring maps `R →+* S ⧸ I ^ n`.
-/
def liftRingHom (f : (n : ℕ) → R →+* S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m) :
    R →+* AdicCompletion I S where
  toFun := fun x ↦ ⟨fun n ↦ (factor (le_of_eq (Ideal.mul_top _).symm)) (f n x),
    fun hkl ↦ by simp [transitionMap, Submodule.factorPow, ← hf hkl]⟩
  map_add' x y := by
    simp only [map_add]
    ext; simp
  map_zero' := by
    simp only [map_zero]
    ext; simp
  map_mul' x y := by
    simp only [mapQ_eq_factor, factor_eq_factor, map_mul]
    ext; simp
  map_one' := by
    simp only [map_one]
    ext; simp

variable (f : (n : ℕ) → R →+* S ⧸ I ^ n)
  (hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m)

set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.factor_eval_liftRingHom** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompleti
on`。
形式化陈述：factor_eval_liftRingHom (n : Nat) (x : R) (h : I ^ n • ⊤ <= I ^ n) : facto
r h (eval I S n (liftRingHom I f hf x)) = f n x
参数：n : Nat；x : R；h : I ^ n • ⊤ <= I ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsTwoSided.instHPowNat`：∀ {R : Type u} [inst : Semiring R] {I : Id
eal R} [I.IsTwoSided] (n : ℕ), (I ^ n).IsTwoSided
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.Quotient.factor_comp_apply`：factor_comp_apply (H1 : S <= T) (H2 : 
T <= U) (x : R ⧸ S) : factor H2 (factor H1 x) = factor (H1.trans H2) x
· 使用定理 `Ideal.Quotient.factor_eq`：factor_eq : factor (le_refl S) = RingHom.id _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factor_eval_liftRingHom (n : ℕ) (x : R) (h : I ^ n • ⊤ ≤ I ^ n) :
    factor h (eval I S n (liftRingHom I f hf x)) = f n x := by
  simp [liftRingHom, eval]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AdicCompletion.eval** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：eval (n : Nat) : AdicCompletion I M ->ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M)
 where toFun f
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evalₐ_liftRingHom (n : ℕ) (x : R) :
    evalₐ I n (liftRingHom I f hf x) = f n x := by
  rw [← factor_eval_eq_evalₐ I _ (le_of_eq (Ideal.mul_top _))]
  simp [liftRingHom, eval]

@[simp]
/-
**AdicCompletion.eval** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：eval (n : Nat) : AdicCompletion I M ->ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M)
 where toFun f
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evalₐ_comp_liftRingHom (n : ℕ) :
    (evalₐ I n : _ →+* _).comp (liftRingHom I f hf) = f n := by
  ext; simp

section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra R S]

/-- `AlgHom` version of `AdicCompletion.liftRingHom`. -/
/-
**AdicCompletion.liftAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：liftAlgHom (f : (n : Nat) -> A ->ₐ[R] S ⧸ I ^ n) (hf : forall {m n : Nat} 
(hle : m <= n), (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f 
n) = f m) : A ->ₐ[R] AdicCompletion I S where __
参数：f : (n : Nat) -> A ->ₐ[R] S ⧸ I ^ n；hf : forall {m n : Nat} (hle : m <= n), (
Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgHom` version of `AdicCompletion.liftRingHom`.
-/
def liftAlgHom (f : (n : ℕ) → A →ₐ[R] S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m) :
    A →ₐ[R] AdicCompletion I S where
  __ := liftRingHom I (fun n ↦ (f n).toRingHom) <| fun hle ↦ by ext x; exact congr($(hf hle) x)
  commutes' r := ext_evalₐ fun n ↦ by
    simp [evalₐ_liftRingHom _ _ <| fun hle ↦ by ext x; exact congr($(hf hle) x)]

variable (f : (n : ℕ) → A →ₐ[R] S ⧸ I ^ n)
  (hf : ∀ {m n : ℕ} (hle : m ≤ n),
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m)

@[simp]
/-
**AdicCompletion.eval** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：eval (n : Nat) : AdicCompletion I M ->ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M)
 where toFun f
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma evalₐ_liftAlgHom (n : ℕ) (x : A) :
    evalₐ I n (liftAlgHom I f hf x) = f n x :=
  evalₐ_liftRingHom _ _ (fun hle ↦ by ext x; exact congr($(hf hle) x)) _ _

@[simp]
/-
**AdicCompletion.evalOne** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma evalOneₐ_liftAlgHom (x : A) :
    evalOneₐ I (liftAlgHom I f hf x) = Ideal.Quotient.factorₐ R (by simp) (f 1 x) := by
  simp [evalOneₐ]

end

variable [IsAdicComplete I S]

/--
When `S` is `I`-adic complete, the canonical map from `S` to
its `I`-adic completion is an `S`-algebra isomorphism.
-/
/-
**AdicCompletion.ofAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：ofAlgEquiv : S ≃ₐ[S] AdicCompletion I S where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `S` is `I`-adic complete, the canonical map from `S` to
its `I`-adic completion is an `S`-algebra isomorphism.
-/
noncomputable def ofAlgEquiv : S ≃ₐ[S] AdicCompletion I S where
  __ := ofLinearEquiv I S
  map_mul' _ _ := by ext; simp
  commutes' _ := rfl

@[simp]
/-
**AdicCompletion.ofAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：ofAlgEquiv_apply (x : S) : ofAlgEquiv I x = of I S x
参数：x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofAlgEquiv_apply (x : S) : ofAlgEquiv I x = of I S x := by
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AdicCompletion.of_ofAlgEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：of_ofAlgEquiv_symm (x : AdicCompletion I S) : of I S ((ofAlgEquiv I).symm 
x) = x
参数：x : AdicCompletion I S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdicCompletion.of_ofLinearEquiv_symm`：of_ofLinearEquiv_symm (x : AdicCom
pletion I M) : of I M ((ofLinearEquiv I M).symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_ofAlgEquiv_symm (x : AdicCompletion I S) :
    of I S ((ofAlgEquiv I).symm x) = x := by
  simp [ofAlgEquiv]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AdicCompletion.ofAlgEquiv_symm_of** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：ofAlgEquiv_symm_of (x : S) : (ofAlgEquiv I).symm (of I S x) = x
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdicCompletion.ofLinearEquiv_symm_of`：ofLinearEquiv_symm_of (x : M) : (o
fLinearEquiv I M).symm (of I M x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofAlgEquiv_symm_of (x : S) :
    (ofAlgEquiv I).symm (of I S x) = x := by
  simp [ofAlgEquiv]

set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.mk_smul_top_ofAlgEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AdicComp
letion`。
形式化陈述：mk_smul_top_ofAlgEquiv_symm (n : Nat) (x : AdicCompletion I S) : Ideal.Quo
tient.mk (I ^ n • ⊤) ((ofAlgEquiv I).symm x) = eval I S n x
参数：n : Nat；x : AdicCompletion I S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AdicCompletion.of_ofAlgEquiv_symm`：of_ofAlgEquiv_symm (x : AdicCompletio
n I S) : of I S ((ofAlgEquiv I).symm x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_smul_top_ofAlgEquiv_symm (n : ℕ) (x : AdicCompletion I S) :
    Ideal.Quotient.mk (I ^ n • ⊤) ((ofAlgEquiv I).symm x) = eval I S n x := by
  nth_rw 2 [← of_ofAlgEquiv_symm I x]
  simp [-of_ofAlgEquiv_symm, eval]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AdicCompletion.mk_ofAlgEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：mk_ofAlgEquiv_symm (n : Nat) (x : AdicCompletion I S) : Ideal.Quotient.mk 
(I ^ n) ((ofAlgEquiv I).symm x) = evalₐ I n x
参数：n : Nat；x : AdicCompletion I S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.ofLinearMap_apply`：∀ {R : Type u} {A : Type v} {B : Type w} [inst
 : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algeb
ra R A] [inst_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AdicCompletion.mk_smul_top_ofAlgEquiv_symm`：mk_smul_top_ofAlgEquiv_symm 
(n : Nat) (x : AdicCompletion I S) : Ideal.Quotient.mk (I ^ n • ⊤) ((ofAlgEquiv 
I).symm x) = eval I S n x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_ofAlgEquiv_symm (n : ℕ) (x : AdicCompletion I S) :
    Ideal.Quotient.mk (I ^ n) ((ofAlgEquiv I).symm x) = evalₐ I n x := by
  simp only [evalₐ, AlgHom.coe_comp, Function.comp_apply, AlgHom.ofLinearMap_apply]
  rw [← mk_smul_top_ofAlgEquiv_symm I n x]
  simp

@[simp]
/-
**AdicCompletion.mk_ofAlgEquiv_symm_eq_evalOne** 是 Mathlib 中的一个引理，位于命名空间 `AdicCo
mpletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_ofAlgEquiv_symm_eq_evalOneₐ (x : AdicCompletion I S) :
    Ideal.Quotient.mk I ((ofAlgEquiv I).symm x) = evalOneₐ I x := by
  simp [evalOneₐ, ← mk_ofAlgEquiv_symm]

end liftRingHom

section

variable {A : Type*} [CommRing A] [Algebra R A] [Algebra R S]

/-- The canonical projection from the `I`-adic completion of `S` to `S ⧸ I`. Defined
in terms of a surjective map `S →ₐ[R] A`. -/
/-
**AdicCompletion.kerProj** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：kerProj {f : S ->ₐ[R] A} (hf : Function.Surjective f) : AdicCompletion (Ri
ngHom.ker f) S ->ₐ[R] A
参数：hf : Function.Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection from the `I`-adic completion of `S` to `S ⧸ I`. Defined
in terms of a surjective map `S →ₐ[R] A`.
-/
noncomputable def kerProj {f : S →ₐ[R] A} (hf : Function.Surjective f) :
    AdicCompletion (RingHom.ker f) S →ₐ[R] A :=
  (Ideal.quotientKerAlgEquivOfSurjective hf).toAlgHom.comp <|
    (AdicCompletion.evalOneₐ <| RingHom.ker f).restrictScalars R

@[simp]
/-
**AdicCompletion.kerProj_of** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：kerProj_of {f : S ->ₐ[R] A} (hf : Function.Surjective f) (x : S) : kerProj
 hf (.of _ _ x) = f x
参数：hf : Function.Surjective f；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
lemma kerProj_of {f : S →ₐ[R] A} (hf : Function.Surjective f) (x : S) :
    kerProj hf (.of _ _ x) = f x :=
  rfl
/-
**AdicCompletion.kerProj_surjective** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：kerProj_surjective {f : S ->ₐ[R] A} (hf : Function.Surjective f) : Functio
n.Surjective (kerProj hf)
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用引理 `AdicCompletion.evalOneₐ_surjective`：evalOneₐ_surjective : Function.Surje
ctive (evalOneₐ I)
-/
lemma kerProj_surjective {f : S →ₐ[R] A} (hf : Function.Surjective f) :
    Function.Surjective (kerProj hf) := by
  dsimp [kerProj]
  exact (AlgEquiv.surjective _).comp (evalOneₐ_surjective _)

end

end AdicCompletion

