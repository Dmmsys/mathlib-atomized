/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Module.Prod

/-!
# The R-algebra structure on products of R-algebras

The R-algebra structure on `(i : I) → A i` when each `A i` is an R-algebra.

## Main definitions

* `Prod.algebra`
* `AlgHom.fst`
* `AlgHom.snd`
* `AlgHom.prod`
* `AlgEquiv.prodUnique` and `AlgEquiv.uniqueProd`
-/

@[expose] public section


variable {R A B C : Type*}
variable [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

namespace Prod

variable (R A B)

open Algebra

/-
**Prod.algebra** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：algebra : Algebra R (A × B) where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebra : Algebra R (A × B) where
  algebraMap := RingHom.prod (algebraMap R A) (algebraMap R B)
  commutes' := by
    rintro r ⟨a, b⟩
    dsimp
    rw [commutes r a, commutes r b]
  smul_def' := by
    rintro r ⟨a, b⟩
    dsimp
    rw [Algebra.smul_def r a, Algebra.smul_def r b]

variable {R A B}

@[simp]
/-
**Prod.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：algebraMap_apply (r : R) : algebraMap R (A × B) r = (algebraMap R A r, alg
ebraMap R B r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply (r : R) : algebraMap R (A × B) r = (algebraMap R A r, algebraMap R B r) :=
  rfl

end Prod

namespace AlgHom

variable (R A B)

/-- First projection as `AlgHom`. -/
/-
**AlgHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：fst : A × B ->ₐ[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
First projection as `AlgHom`.
-/
def fst : A × B →ₐ[R] A :=
  { RingHom.fst A B with commutes' := fun _r => rfl }

/-- Second projection as `AlgHom`. -/
/-
**AlgHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：snd : A × B ->ₐ[R] B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Second projection as `AlgHom`.
-/
def snd : A × B →ₐ[R] B :=
  { RingHom.snd A B with commutes' := fun _r => rfl }

variable {A B}

@[simp]
/-
**AlgHom.fst_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：fst_apply (a) : fst R A B a = a.1
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_apply (a) : fst R A B a = a.1 := rfl

@[simp]
/-
**AlgHom.snd_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：snd_apply (a) : snd R A B a = a.2
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_apply (a) : snd R A B a = a.2 := rfl

variable {R}

/-- The `Function.prod` of two morphisms is a morphism. -/
@[simps!]
/-
**AlgHom.prod** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：prod (f : A ->ₐ[R] B) (g : A ->ₐ[R] C) : A ->ₐ[R] B × C
参数：f : A ->ₐ[R] B；g : A ->ₐ[R] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Function.prod` of two morphisms is a morphism.
-/
def prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : A →ₐ[R] B × C :=
  { f.toRingHom.prod g.toRingHom with
    commutes' := fun r => by
      simp only [toRingHom_eq_coe, RingHom.toFun_eq_coe, RingHom.prod_apply, coe_toRingHom,
        commutes, Prod.algebraMap_apply] }
/-
**AlgHom.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_prod (f : A ->ₐ[R] B) (g : A ->ₐ[R] C) : ⇑(f.prod g) = Function.prod f
 g
参数：f : A ->ₐ[R] B；g : A ->ₐ[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[simp]
/-
**AlgHom.fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：fst_prod (f : A ->ₐ[R] B) (g : A ->ₐ[R] C) : (fst R B C).comp (prod f g) =
 f
参数：f : A ->ₐ[R] B；g : A ->ₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
theorem fst_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : (fst R B C).comp (prod f g) = f := by ext; rfl

@[simp]
/-
**AlgHom.snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：snd_prod (f : A ->ₐ[R] B) (g : A ->ₐ[R] C) : (snd R B C).comp (prod f g) =
 g
参数：f : A ->ₐ[R] B；g : A ->ₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
theorem snd_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : (snd R B C).comp (prod f g) = g := by ext; rfl

@[simp]
/-
**AlgHom.prod_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：prod_fst_snd : prod (fst R A B) (snd R A B) = AlgHom.id R _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = AlgHom.id R _ := rfl
/-
**AlgHom.prod_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：prod_comp {C' : Type*} [Semiring C'] [Algebra R C'] (f : A ->ₐ[R] B) (g : 
B ->ₐ[R] C) (g' : B ->ₐ[R] C') : (g.prod g').comp f = (g.comp f).prod (g'.comp f
)
参数：f : A ->ₐ[R] B；g : B ->ₐ[R] C；g' : B ->ₐ[R] C'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_comp {C' : Type*} [Semiring C'] [Algebra R C']
    (f : A →ₐ[R] B) (g : B →ₐ[R] C) (g' : B →ₐ[R] C') :
    (g.prod g').comp f = (g.comp f).prod (g'.comp f) := rfl

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
/-
**AlgHom.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：prodEquiv : (A ->ₐ[R] B) × (A ->ₐ[R] C) ≃ (A ->ₐ[R] B × C) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the product of two maps with the same domain is equivalent to taking the 
product of
their codomains.
-/
def prodEquiv : (A →ₐ[R] B) × (A →ₐ[R] C) ≃ (A →ₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)

/-- `Prod.map` of two algebra homomorphisms. -/
/-
**AlgHom.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：prodMap {D : Type*} [Semiring D] [Algebra R D] (f : A ->ₐ[R] B) (g : C ->ₐ
[R] D) : A × C ->ₐ[R] B × D
参数：f : A ->ₐ[R] B；g : C ->ₐ[R] D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.map` of two algebra homomorphisms.
-/
def prodMap {D : Type*} [Semiring D] [Algebra R D] (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
    A × C →ₐ[R] B × D :=
  { toRingHom := f.toRingHom.prodMap g.toRingHom
    commutes' := fun r => by simp [commutes] }

end AlgHom

namespace AlgEquiv

section

variable {S T A B : Type*} [Semiring A] [Semiring B]
  [Semiring S] [Semiring T] [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B]

/-- Product of algebra isomorphisms. -/
/-
**AlgEquiv.prodCongr** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：prodCongr (l : S ≃ₐ[R] A) (r : T ≃ₐ[R] B) : (S × T) ≃ₐ[R] A × B
参数：l : S ≃ₐ[R] A；r : T ≃ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of algebra isomorphisms.
-/
def prodCongr (l : S ≃ₐ[R] A) (r : T ≃ₐ[R] B) : (S × T) ≃ₐ[R] A × B :=
  .ofRingEquiv (f := RingEquiv.prodCongr l r) <| by simp

variable (l : S ≃ₐ[R] A) (r : T ≃ₐ[R] B)

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/-
**AlgEquiv.prodCongr_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：prodCongr_apply (x : S × T) : prodCongr l r x = Equiv.prodCongr l r x
参数：x : S × T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prodCongr_apply (x : S × T) : prodCongr l r x = Equiv.prodCongr l r x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/-
**AlgEquiv.prodCongr_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgEquiv`。
形式化陈述：prodCongr_symm_apply (x : A × B) : (prodCongr l r).symm x = (Equiv.prodCon
gr l r).symm x
参数：x : A × B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prodCongr_symm_apply (x : A × B) :
    (prodCongr l r).symm x = (Equiv.prodCongr l r).symm x := rfl

end

/-- Multiplying by the trivial algebra from the right does not change the structure.
This is the `AlgEquiv` version of `LinearEquiv.prodUnique` and `RingEquiv.prodZeroRing.symm`. -/
@[simps!]
/-
**AlgEquiv.prodUnique** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：prodUnique [Unique B] : (A × B) ≃ₐ[R] A where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
Multiplying by the trivial algebra from the right does not change the structure.
This is the `AlgEquiv` version of `LinearEquiv.prodUnique` and `RingEquiv.prodZe
roRing.symm`.
-/
def prodUnique [Unique B] : (A × B) ≃ₐ[R] A where
  toFun := Prod.fst
  invFun x := (x, 0)
  __ := (RingEquiv.prodZeroRing A B).symm
  commutes' _ := rfl

/-- Multiplying by the trivial algebra from the left does not change the structure.
This is the `AlgEquiv` version of `LinearEquiv.uniqueProd` and `RingEquiv.zeroRingProd.symm`.
-/
@[simps!]
/-
**AlgEquiv.uniqueProd** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：uniqueProd [Unique B] : (B × A) ≃ₐ[R] A where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
Multiplying by the trivial algebra from the left does not change the structure.
This is the `AlgEquiv` version of `LinearEquiv.uniqueProd` and `RingEquiv.zeroRi
ngProd.symm`.
-/
def uniqueProd [Unique B] : (B × A) ≃ₐ[R] A where
  toFun := Prod.snd
  invFun x := (0, x)
  __ := (RingEquiv.zeroRingProd A B).symm
  commutes' _ := rfl

end AlgEquiv

