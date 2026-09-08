/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# The adele ring of a number field

This file contains the formalisation of the adele ring of a number field as the
direct product of the infinite adele ring and the finite adele ring.

## Main definitions

- `NumberField.AdeleRing K` is the adele ring of a number field `K`.
- `NumberField.AdeleRing.principalSubgroup K` is the subgroup of principal adeles `(x)ᵥ`.

## References
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
adele ring, number field
-/

@[expose] public section

noncomputable section

namespace NumberField

open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion IsDedekindDomain

/-! ## The adele ring  -/

/-- `AdeleRing (𝓞 K) K` is the adele ring of a number field `K`.

More generally `AdeleRing R K` can be used if `K` is the field of fractions
of the Dedekind domain `R`. This enables use of rings like `AdeleRing ℤ ℚ`, which
in practice are easier to work with than `AdeleRing (𝓞 ℚ) ℚ`.

Note that this definition does not give the correct answer in the function field case.
-/
/-
**NumberField.AdeleRing** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：AdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algeb
ra R K] [IsFractionRing R K]
参数：R K : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AdeleRing (𝓞 K) K` is the adele ring of a number field `K`.

More generally `AdeleRing R K` can be used if `K` is the field of fractions
of the Dedekind domain `R`. This enables use of rings like `AdeleRing ℤ ℚ`, whic
h
in practice are easier to work with than `AdeleRing (𝓞 ℚ) ℚ`.

Note that this definition does not give the correct answer in the function field
 case.
-/
def AdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] := InfiniteAdeleRing K × FiniteAdeleRing R K
deriving CommRing, TopologicalSpace, IsTopologicalRing, Algebra K

namespace AdeleRing

/-- `𝔸ᶠ[K]` is notation for `IsDedekindDomain.FiniteAdeleRing (𝓞 K) K`. -/
scoped notation:max "𝔸ᶠ[" K "]" => FiniteAdeleRing (𝓞 K) K
/-- `𝔸[R, K]` is notation for `NumberField.AdeleRing R K`. -/
scoped notation:max "𝔸[" R ", " K "]" => AdeleRing R K
/-- `𝔸[K]` is notation for `NumberField.AdeleRing (𝓞 K) K`. -/
scoped notation:max "𝔸[" K "]" => AdeleRing (𝓞 K) K

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-
**NumberField.AdeleRing.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.AdeleRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited 𝔸[R, K] := ⟨0⟩

@[simp]
/-
**NumberField.AdeleRing.algebraMap_fst_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.AdeleRing`。
形式化陈述：algebraMap_fst_apply (x : K) (v : InfinitePlace K) : (algebraMap K 𝔸[R, K]
 x).1 v = x
参数：x : K；v : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_fst_apply (x : K) (v : InfinitePlace K) :
    (algebraMap K 𝔸[R, K] x).1 v = x := rfl

@[simp]
/-
**NumberField.AdeleRing.algebraMap_snd_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.AdeleRing`。
形式化陈述：algebraMap_snd_apply (x : K) (v : HeightOneSpectrum R) : (algebraMap K 𝔸[R
, K] x).2 v = x
参数：x : K；v : HeightOneSpectrum R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_snd_apply (x : K) (v : HeightOneSpectrum R) :
    (algebraMap K 𝔸[R, K] x).2 v = x := rfl
/-
**NumberField.AdeleRing.algebraMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.AdeleRing`。
形式化陈述：algebraMap_injective [NumberField K] : Function.Injective (algebraMap K 𝔸[
R, K])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `NumberField.InfiniteAdeleRing.instNontrivial`：∀ (K : Type u_1) [inst : F
ield K] [NumberField K], Nontrivial (NumberField.InfiniteAdeleRing K)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
-/
theorem algebraMap_injective [NumberField K] : Function.Injective (algebraMap K 𝔸[R, K]) :=
  fun _ _ hxy => (algebraMap K K∞).injective (Prod.ext_iff.1 hxy).1

/-- The subgroup of principal adeles `(x)ᵥ` where `x ∈ K`. -/
/-
**NumberField.AdeleRing.principalSubgroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberFie
ld.AdeleRing`。
形式化陈述：principalSubgroup : AddSubgroup 𝔸[R, K]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup of principal adeles `(x)ᵥ` where `x ∈ K`.
-/
abbrev principalSubgroup : AddSubgroup 𝔸[R, K] := (algebraMap K 𝔸[R, K]).range.toAddSubgroup

end AdeleRing

end NumberField

