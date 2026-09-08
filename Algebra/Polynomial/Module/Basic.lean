/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Polynomial.Module.AEval

/-!
# Polynomial module

In this file, we define the polynomial module for an `R`-module `M`, i.e. the `R[X]`-module `M[X]`.

This is defined as a type alias `PolynomialModule R M := ℕ →₀ M`, since there might be different
module structures on `ℕ →₀ M` of interest. See the docstring of `PolynomialModule` for details.
-/

@[expose] public noncomputable section
universe u v
open Polynomial

/-- The `R[X]`-module `M[X]` for an `R`-module `M`.
This is isomorphic (as an `R`-module) to `M[X]` when `M` is a ring.

We require all the module instances `Module S (PolynomialModule R M)` to factor through `R` except
`Module R[X] (PolynomialModule R M)`.
In this constraint, we have the following instances for example :
- `R` acts on `PolynomialModule R R[X]`
- `R[X]` acts on `PolynomialModule R R[X]` as `R[Y]` acting on `R[X][Y]`
- `R` acts on `PolynomialModule R[X] R[X]`
- `R[X]` acts on `PolynomialModule R[X] R[X]` as `R[X]` acting on `R[X][Y]`
- `R[X][X]` acts on `PolynomialModule R[X] R[X]` as `R[X][Y]` acting on itself

This is also the reason why `R` is included in the alias, or else there will be two different
instances of `Module R[X] (PolynomialModule R[X])`.

See https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2315065.20polynomial.20modules
for the full discussion.
-/
@[nolint unusedArguments]
/-
**PolynomialModule** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → (M : Type u_2) → [inst : CommRing R] → [inst_1 : AddCommG
roup M] → [_root_.Module R M] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R[X]`-module `M[X]` for an `R`-module `M`.
This is isomorphic (as an `R`-module) to `M[X]` when `M` is a ring.

We require all the module instances `Module S (PolynomialModule R M)` to factor 
through `R` except
`Module R[X] (PolynomialModule R M)`.
In this constraint, we have the following instances for example :
- `R` acts on `PolynomialModule R R[X]`
- `R[X]` acts on `PolynomialModule R R[X]` as `R[Y]` acting on `R[X][Y]`
- `R` acts on `PolynomialModule R[X] R[X]`
- `R[X]` acts on `PolynomialModule R[X] R[X]` as `R[X]` acting on `R[X][Y]`
- `R[X][X]` acts on `PolynomialModule R[X] R[X]` as `R[X][Y]` acting on itself

This is also the reason why `R` is included in the alias, or else there will be 
two different
instances of `Module R[X] (PolynomialModule R[X])`.

See https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.231
5065.20polynomial.20modules
for the full discussion.
-/
structure PolynomialModule (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  /-- Construct an element of the polynomial module `M[[]]` from its coefficients `ℕ →₀ M`. -/
  ofCoeff (R) ::
  /-- The coefficients `ℕ →₀ M` of an element of the additive monoid algebra `M[X]`. -/
  coeff : ℕ →₀ M

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

namespace PolynomialModule
variable {x y : PolynomialModule R M} {r r₁ r₂ : R} {m m' m₁ m₂ m₁' m₂' : M}

/-
**PolynomialModule.coeff_ofCoeff** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModule`。
形式化陈述：coeff_ofCoeff (x : Nat ->₀ M) : (ofCoeff R x).coeff = x
参数：x : Nat ->₀ M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeff_ofCoeff (x : ℕ →₀ M) : (ofCoeff R x).coeff = x := rfl
/-
**PolynomialModule.ofCoeff_coeff** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModule`。
形式化陈述：ofCoeff_coeff (x : PolynomialModule R M) : ofCoeff R x.coeff = x
参数：x : PolynomialModule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofCoeff_coeff (x : PolynomialModule R M) : ofCoeff R x.coeff = x := rfl

variable (R) in
/-- `PolynomialModule.coeff` as an equiv. -/
@[simps! apply symm_apply]
/-
**PolynomialModule.coeffEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialModule`。
形式化陈述：coeffEquiv : PolynomialModule R M ≃ (Nat ->₀ M) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PolynomialModule.coeff` as an equiv.
-/
def coeffEquiv : PolynomialModule R M ≃ (ℕ →₀ M) where
  toFun := coeff
  invFun := ofCoeff R
  left_inv _ := rfl
  right_inv _ := rfl
/-
**PolynomialModule.** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma «forall» {P : PolynomialModule R M → Prop} : (∀ p, P p) ↔ ∀ q, P (ofCoeff R q) :=
  (coeffEquiv R).forall_congr_left
/-
**PolynomialModule.** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma «exists» {P : PolynomialModule R M → Prop} : (∃ p, P p) ↔ ∃ q, P (ofCoeff R q) :=
  (coeffEquiv R).exists_congr_left
/-
**PolynomialModule.coeff_injective** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModule`。
形式化陈述：coeff_injective : (coeff : PolynomialModule R M -> Nat ->₀ M).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma coeff_injective : (coeff : PolynomialModule R M → ℕ →₀ M).Injective :=
  (coeffEquiv R).injective
/-
**PolynomialModule.ofCoeff_injective** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModule
`。
形式化陈述：ofCoeff_injective : (ofCoeff R : (Nat ->₀ M) -> PolynomialModule R M).Inje
ctive
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma ofCoeff_injective : (ofCoeff R : (ℕ →₀ M) → PolynomialModule R M).Injective :=
  (coeffEquiv R).symm.injective

@[simp]
/-
**PolynomialModule.coeff_inj** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModule`。
形式化陈述：coeff_inj : x.coeff = y.coeff ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `PolynomialModule.coeff_injective`：coeff_injective : (coeff : PolynomialM
odule R M -> Nat ->₀ M).Injective
-/
lemma coeff_inj : x.coeff = y.coeff ↔ x = y := coeff_injective.eq_iff
/-
**PolynomialModule.ofCoeff_inj** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModule`。
形式化陈述：ofCoeff_inj {x y : Nat ->₀ M} : ofCoeff R x = ofCoeff R y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `PolynomialModule.ofCoeff_injective`：ofCoeff_injective : (ofCoeff R : (Na
t ->₀ M) -> PolynomialModule R M).Injective
-/
lemma ofCoeff_inj {x y : ℕ →₀ M} : ofCoeff R x = ofCoeff R y ↔ x = y := ofCoeff_injective.eq_iff

@[ext] alias ⟨ext, _⟩ := coeff_inj
/-
**PolynomialModule.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialModule`。
形式化陈述：instInhabited : Inhabited (PolynomialModule R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance instInhabited : Inhabited (PolynomialModule R M) := fast_instance% (coeffEquiv R).inhabited
/-
**PolynomialModule.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialModule`。
形式化陈述：instNontrivial [Nontrivial M] : Nontrivial (PolynomialModule R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
instance instNontrivial [Nontrivial M] : Nontrivial (PolynomialModule R M) :=
  (coeffEquiv R).nontrivial
/-
**PolynomialModule.instUnique** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialModule`。
形式化陈述：instUnique [Subsingleton M] : Unique (PolynomialModule R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance instUnique [Subsingleton M] : Unique (PolynomialModule R M) := fast_instance%
  (coeffEquiv R).unique
/-
**PolynomialModule.instDecidableEq** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialModule`。
形式化陈述：instDecidableEq [DecidableEq M] : DecidableEq (PolynomialModule R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableEq [DecidableEq M] : DecidableEq (PolynomialModule R M) :=
  (coeffEquiv R).decidableEq
/-
**PolynomialModule.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialModule`
。
形式化陈述：instAddCommGroup : AddCommGroup (PolynomialModule R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup : AddCommGroup (PolynomialModule R M) := fast_instance%
  (coeffEquiv R).addCommGroup

/-- `PolynomialModule.coeff` as an `AddEquiv`. -/
@[simps! apply symm_apply]
/-
**PolynomialModule.coeffAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialModule`。
形式化陈述：coeffAddEquiv : PolynomialModule R M ≃+ (Nat ->₀ M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PolynomialModule.coeff` as an `AddEquiv`.
-/
def coeffAddEquiv : PolynomialModule R M ≃+ (ℕ →₀ M) := (coeffEquiv R).addEquiv
/-
**PolynomialModule.coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M],   PolynomialModule.coeff 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coeff_zero : coeff (0 : PolynomialModule R M) = 0 := rfl
/-
**PolynomialModule.ofCoeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M],   { coeff := 0 } = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofCoeff_zero : (ofCoeff R 0 : PolynomialModule R M) = 0 := rfl
/-
**PolynomialModule.coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {x : PolynomialModule R M}, x.coeff = 0 ↔ x =
 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PolynomialModule.coeff_inj`：coeff_inj : x.coeff = y.coeff ↔ x = y
-/
@[simp] lemma coeff_eq_zero : coeff x = 0 ↔ x = 0 := coeff_inj
/-
**PolynomialModule.ofCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] {x : ℕ →₀ M},   { coeff := x } = 0 ↔ x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PolynomialModule.ofCoeff_inj`：ofCoeff_inj {x y : Nat ->₀ M} : ofCoeff R 
x = ofCoeff R y ↔ x = y
-/
@[simp] lemma ofCoeff_eq_zero {x : ℕ →₀ M} : ofCoeff R x = 0 ↔ x = 0 :=
  ofCoeff_inj
/-
**PolynomialModule.coeff_add** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   (x y : PolynomialModule R M), (x + y).coeff =
 x.coeff + y.coeff
参数：x y : PolynomialModule R M；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coeff_add (x y : PolynomialModule R M) : coeff (x + y) = coeff x + coeff y := rfl
/-
**PolynomialModule.ofCoeff_add** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   (x y : ℕ →₀ M), { coeff := x + y } = { coeff 
:= x } + { coeff := y }
参数：x y : ℕ →₀ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofCoeff_add (x y : ℕ →₀ M) : ofCoeff R (x + y) = ofCoeff R x + ofCoeff R y := rfl

@[simp]
/-
**PolynomialModule.coeff_sum** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModule`。
形式化陈述：coeff_sum (s : Finset ι) (f : ι -> PolynomialModule R M) : coeff (∑ i in s
, f i) = ∑ i in s, coeff (f i)
参数：s : Finset ι；f : ι -> PolynomialModule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma coeff_sum (s : Finset ι) (f : ι → PolynomialModule R M) :
    coeff (∑ i ∈ s, f i) = ∑ i ∈ s, coeff (f i) := map_sum coeffAddEquiv ..

@[simp]
/-
**PolynomialModule.ofCoeff_sum** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModule`。
形式化陈述：ofCoeff_sum (s : Finset ι) (f : ι -> Nat ->₀ M) : ofCoeff R (∑ i in s, f i
) = ∑ i in s, ofCoeff R (f i)
参数：s : Finset ι；f : ι -> Nat ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma ofCoeff_sum (s : Finset ι) (f : ι → ℕ →₀ M) :
    ofCoeff R (∑ i ∈ s, f i) = ∑ i ∈ s, ofCoeff R (f i) := map_sum coeffAddEquiv.symm ..

@[simp]
/-
**PolynomialModule.coeff_finsuppSum** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModule`
。
形式化陈述：coeff_finsuppSum [AddCommMonoid N] (f : ι ->₀ N) (g : ι -> N -> Polynomial
Module R M) : coeff (f.sum g) = f.sum (fun i n => coeff (g i n))
参数：f : ι ->₀ N；g : ι -> N -> PolynomialModule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma coeff_finsuppSum [AddCommMonoid N] (f : ι →₀ N) (g : ι → N → PolynomialModule R M) :
    coeff (f.sum g) = f.sum (fun i n ↦ coeff (g i n)) := map_finsuppSum coeffAddEquiv ..

@[simp]
/-
**PolynomialModule.ofCoeff_finsuppSum** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModul
e`。
形式化陈述：ofCoeff_finsuppSum [AddCommMonoid N] (f : ι ->₀ N) (g : ι -> N -> Nat ->₀ 
M) : ofCoeff R (f.sum g) = f.sum (fun i n => ofCoeff R (g i n))
参数：f : ι ->₀ N；g : ι -> N -> Nat ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma ofCoeff_finsuppSum [AddCommMonoid N] (f : ι →₀ N) (g : ι → N → ℕ →₀ M) :
    ofCoeff R (f.sum g) = f.sum (fun i n ↦ ofCoeff R (g i n)) :=
  map_finsuppSum coeffAddEquiv.symm ..

variable (R) in
/-- `MonoidAlgebra.single n m` for `m : M`, `r : R` is the element `rm : PolynomialModule R M`. -/
/-
**PolynomialModule.single** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialModule`。
形式化陈述：single (n : Nat) (m : M) : PolynomialModule R M
参数：n : Nat；m : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoidAlgebra.single n m` for `m : M`, `r : R` is the element `rm : PolynomialM
odule R M`.
-/
def single (n : ℕ) (m : M) : PolynomialModule R M := .ofCoeff R <| .single n m
/-
**PolynomialModule.coeff_single** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] (n : ℕ)   (m : M), (PolynomialModule.single R n
 m).coeff = fun₀ | n => m
参数：n : ℕ；m : M；PolynomialModule.single R n m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coeff_single (n : ℕ) (m : M) : (single R n m).coeff = .single n m := rfl
/-
**PolynomialModule.ofCoeff_single** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] (n : ℕ)   (m : M), { coeff := fun₀ | n => m } =
 PolynomialModule.single R n m
参数：n : ℕ；m : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofCoeff_single (n : ℕ) (m : M) : ofCoeff R (.single n m) = single R n m := rfl

@[deprecated (since := "2026-06-18")] alias single_apply := coeff_single
/-
**PolynomialModule.single_zero** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] (n : ℕ),   PolynomialModule.single R n 0 = 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma single_zero (n : ℕ) : single R n (0 : M) = 0 := by simp [single]

@[simp]
/-
**PolynomialModule.single_add** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModule`。
形式化陈述：single_add (n : Nat) (m₁ m₂ : M) : single R n (m₁ + m₂) = single R n m₁ + 
single R n m₂
参数：n : Nat；m₁ m₂ : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialModule.ext`：∀ {R : Type u_2} {M : Type u_3} [inst : CommRing R
] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {x y : PolynomialModu
le R M}, x…
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma single_add (n : ℕ) (m₁ m₂ : M) :
    single R n (m₁ + m₂) = single R n m₁ + single R n m₂ := by ext; simp

/-- This is required to have the `IsScalarTower S R M` instance to avoid diamonds. -/
/-
**PolynomialModule.** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is required to have the `IsScalarTower S R M` instance to avoid diamonds.
-/
instance : Module S (PolynomialModule R M) := (coeffEquiv R).module _
/-
**PolynomialModule.** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M] :
    IsScalarTower S R (PolynomialModule R M) := (coeffEquiv R).isScalarTower _ _

variable (R S) in
/-- `PolynomialModule.coeff` as a linear equiv. -/
@[simps! apply symm_apply]
/-
**PolynomialModule.coeffLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialModule`
。
形式化陈述：coeffLinearEquiv : PolynomialModule R M ≃ₗ[S] Nat ->₀ M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PolynomialModule.coeff` as a linear equiv.
-/
def coeffLinearEquiv : PolynomialModule R M ≃ₗ[S] ℕ →₀ M := (coeffEquiv _).linearEquiv _

variable (R) in
/-- `PolynomialModule.single` as a linear map. -/
/-
**PolynomialModule.lsingle** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialModule`。
形式化陈述：lsingle (i : Nat) : M ->ₗ[R] PolynomialModule R M
参数：i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PolynomialModule.single` as a linear map.
-/
def lsingle (i : ℕ) : M →ₗ[R] PolynomialModule R M :=
  (coeffLinearEquiv R R).symm.comp <| Finsupp.lsingle i
/-
**PolynomialModule.lsingle_apply** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：lsingle_apply (i : Nat) (m : M) (n : Nat) : (lsingle R i m).coeff n = ite 
(i = n) m 0
参数：i : Nat；m : M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
-/
theorem lsingle_apply (i : ℕ) (m : M) (n : ℕ) : (lsingle R i m).coeff n = ite (i = n) m 0 :=
  Finsupp.single_apply
/-
**PolynomialModule.single_smul** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：single_smul (i : Nat) (r : R) (m : M) : single R i (r • m) = r • single R 
i m
参数：i : Nat；r : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
theorem single_smul (i : ℕ) (r : R) (m : M) : single R i (r • m) = r • single R i m :=
  (lsingle R i).map_smul r m

@[elab_as_elim]
/-
**PolynomialModule.induction_linear** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModule`
。
形式化陈述：induction_linear {p : PolynomialModule R M -> Prop} (x : PolynomialModule 
R M) (zero : p 0) (add : forall x y : PolynomialModule R M, p x -> p y -> p (x +
 y)) (single : forall n m, p (single R n m)) : p x
参数：x : PolynomialModule R M；zero : p 0；add : forall x y : PolynomialModule R M, 
p x -> p y -> p (x + y)；single : forall n m, p (single R n m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.induction_linear`：induction_linear {motive : (ι ->₀ M) -> Prop} 
(f : ι ->₀ M) (zero : motive 0) (add : forall f g : ι ->₀ M, motive f -> motive 
g -> motive (f…
-/
lemma induction_linear {p : PolynomialModule R M → Prop} (x : PolynomialModule R M) (zero : p 0)
    (add : ∀ x y : PolynomialModule R M, p x → p y → p (x + y))
    (single : ∀ n m, p (single R n m)) : p x :=
  Finsupp.induction_linear (motive := (p <| ofCoeff R ·)) x.coeff zero (fun _ _ ↦ add _ _)
    (fun _ _ ↦ single _ _)
/-
**PolynomialModule.polynomialModule** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialModule`
。
形式化陈述：polynomialModule : Module R[X] (PolynomialModule R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance polynomialModule : Module R[X] (PolynomialModule R M) :=
  inferInstanceAs <| Module R[X] <| Module.AEval' <| (coeffLinearEquiv R R).symm.comp <|
    (Finsupp.lmapDomain M R Nat.succ).comp (coeffLinearEquiv R R).toLinearMap
/-
**PolynomialModule.smul_def** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialModule`。
形式化陈述：smul_def (f : R[X]) (m : PolynomialModule R M) : f • m = aeval ((coeffLine
arEquiv R R).symm.comp <| (Finsupp.lmapDomain M R Nat.succ).comp (coeffLinearEqu
iv R R).toLinearMap) f m
参数：f : R[X]；m : PolynomialModule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_def (f : R[X]) (m : PolynomialModule R M) :
    f • m = aeval ((coeffLinearEquiv R R).symm.comp <|
    (Finsupp.lmapDomain M R Nat.succ).comp (coeffLinearEquiv R R).toLinearMap) f m := by
  rfl
/-
**PolynomialModule.isScalarTower'** 是 Mathlib 中的一个实例，位于命名空间 `PolynomialModule`。
形式化陈述：isScalarTower' (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [Is
ScalarTower S R M] : IsScalarTower S R[X] (PolynomialModule R M)
参数：M : Type u。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_smul`：algebraMap_smul [SMul R M] [IsScalarTower
 R A M] (r : R) (x : M) : algebraMap R A r • x = r • x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `PolynomialModule.instIsScalarTower`：∀ {R : Type u_2} [inst : CommRing R]
 {S : Type u_5} [inst_1 : CommSemiring S] [inst_2 : Algebra S R] (M : Type u)   
[inst_3 : AddCommGroup M…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower' (M : Type u) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower S R M] : IsScalarTower S R[X] (PolynomialModule R M) := by
  have : IsScalarTower R R[X] (PolynomialModule R M) :=
    inferInstanceAs <| IsScalarTower R R[X] <| Module.AEval' <| (coeffLinearEquiv R R).symm.comp <|
    (Finsupp.lmapDomain M R Nat.succ).comp (coeffLinearEquiv R R).toLinearMap
  constructor
  intro x y z
  rw [← @IsScalarTower.algebraMap_smul S R, ← @IsScalarTower.algebraMap_smul S R, smul_assoc]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PolynomialModule.monomial_smul_single** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialMod
ule`。
形式化陈述：monomial_smul_single (i : Nat) (r : R) (j : Nat) (m : M) : monomial i r • 
single R j m = single R (i + j) (r • m)
参数：i : Nat；r : R；j : Nat；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PolynomialModule.instIsScalarTower`：∀ {R : Type u_2} [inst : CommRing R]
 {S : Type u_5} [inst_1 : CommSemiring S] [inst_2 : Algebra S R] (M : Type u)   
[inst_3 : AddCommGroup M…
· 使用引理 `PolynomialModule.smul_def`：smul_def (f : R[X]) (m : PolynomialModule R M
) : f • m = aeval ((coeffLinearEquiv R R).symm.comp <| (Finsupp.lmapDomain M R N
at.succ).comp (…
· 使用定理 `Polynomial.aeval_monomial`：aeval_monomial {n : Nat} {r : R} : aeval x (m
onomial n r) = algebraMap _ _ r * x ^ n
· 使用定理 `Module.End.pow_apply`：pow_apply (f : End R M) (n : Nat) (m : M) : (f ^ n
) m = f^[n] m
· 使用定理 `Function.iterate_zero`：iterate_zero : f^[0] = id
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `Function.iterate_succ`：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.one_add`：∀ (n : ℕ), 1 + n = n.succ
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
-/
theorem monomial_smul_single (i : ℕ) (r : R) (j : ℕ) (m : M) :
    monomial i r • single R j m = single R (i + j) (r • m) := by
  simp only [Module.End.mul_apply, Polynomial.aeval_monomial, Module.End.pow_apply,
    Module.algebraMap_end_apply, smul_def]
  induction i generalizing r j m with
  | zero =>
    rw [Function.iterate_zero, zero_add]
    exact congr(ofCoeff R $(Finsupp.smul_single r j m))
  | succ n hn =>
    rw [Function.iterate_succ, Function.comp_apply, add_assoc, ← hn]
    congr 2
    rw [Nat.one_add]
    exact congr(ofCoeff R $(Finsupp.mapDomain_single))

@[simp]
/-
**PolynomialModule.monomial_smul_lsingle** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialMo
dule`。
形式化陈述：monomial_smul_lsingle (i : Nat) (r : R) (j : Nat) (m : M) : (monomial i) r
 • lsingle R j m = lsingle R (i + j) (r • m)
参数：i : Nat；r : R；j : Nat；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialModule.monomial_smul_single`：monomial_smul_single (i : Nat) (r
 : R) (j : Nat) (m : M) : monomial i r • single R j m = single R (i + j) (r • m)
-/
theorem monomial_smul_lsingle (i : ℕ) (r : R) (j : ℕ) (m : M) :
    (monomial i) r • lsingle R j m = lsingle R (i + j) (r • m) :=
  monomial_smul_single ..

@[simp]
/-
**PolynomialModule.monomial_smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModu
le`。
形式化陈述：monomial_smul_apply (i : Nat) (r : R) (g : PolynomialModule R M) (n : Nat)
 : (monomial i r • g).coeff n = ite (i <= n) (r • g.coeff (n - i)) 0
参数：i : Nat；r : R；g : PolynomialModule R M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PolynomialModule.induction_linear`：induction_linear {p : PolynomialModul
e R M -> Prop} (x : PolynomialModule R M) (zero : p 0) (add : forall x y : Polyn
omialModule R M, p x ->…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `ite_add_ite`：∀ {α : Type u_2} (P : Prop) [inst : Decidable P] [inst_1 : 
Add α] (a b c d : α),   ((if P then a else b) + if P then c else d) = if P then 
a…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `PolynomialModule.monomial_smul_single`：monomial_smul_single (i : Nat) (r
 : R) (j : Nat) (m : M) : monomial i r • single R j m = single R (i + j) (r • m)
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
-/
theorem monomial_smul_apply (i : ℕ) (r : R) (g : PolynomialModule R M) (n : ℕ) :
    (monomial i r • g).coeff n = ite (i ≤ n) (r • g.coeff (n - i)) 0 := by
  induction g using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp [smul_add, hp, hq, ite_add_ite]
  | single =>
    simp [monomial_smul_single, Finsupp.single_apply]
    grind

@[simp]
/-
**PolynomialModule.smul_single_apply** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule
`。
形式化陈述：smul_single_apply (i : Nat) (f : R[X]) (m : M) (n : Nat) : (f • single R i
 m).coeff n = ite (i <= n) (f.coeff (n - i) • m) 0
参数：i : Nat；f : R[X]；m : M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `ite_add_ite`：∀ {α : Type u_2} (P : Prop) [inst : Decidable P] [inst_1 : 
Add α] (a b c d : α),   ((if P then a else b) + if P then c else d) = if P then 
a…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PolynomialModule.monomial_smul_single`：monomial_smul_single (i : Nat) (r
 : R) (j : Nat) (m : M) : monomial i r • single R j m = single R (i + j) (r • m)
-/
theorem smul_single_apply (i : ℕ) (f : R[X]) (m : M) (n : ℕ) :
    (f • single R i m).coeff n = ite (i ≤ n) (f.coeff (n - i) • m) 0 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_smul, hp, hq, ite_add_ite]
  | monomial => simp; grind [monomial_smul_single, coeff_monomial, zero_smul]
/-
**PolynomialModule.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：smul_apply (f : R[X]) (g : PolynomialModule R M) (n : Nat) : (f • g).coeff
 n = ∑ x in Finset.antidiagonal n, f.coeff x.1 • g.coeff x.2
参数：f : R[X]；g : PolynomialModule R M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`：∀ {M : Type u_3} [inst : 
AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidi
agonal n, f ij.1 ij.2 = ∑ k ∈ Finse…
· 使用定理 `PolynomialModule.monomial_smul_apply`：monomial_smul_apply (i : Nat) (r :
 R) (g : PolynomialModule R M) (n : Nat) : (monomial i r • g).coeff n = ite (i <
= n) (r • g.coeff (n - i))…
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
-/
theorem smul_apply (f : R[X]) (g : PolynomialModule R M) (n : ℕ) :
    (f • g).coeff n = ∑ x ∈ Finset.antidiagonal n, f.coeff x.1 • g.coeff x.2 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_smul, hp, hq, ← Finset.sum_add_distrib]
  | monomial f_n f_a =>
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j =>
      (monomial f_n f_a).coeff i • g.coeff j, monomial_smul_apply]
    simp [Polynomial.coeff_monomial]

set_option backward.isDefEq.respectTransparency false in
/-- `PolynomialModule R R` is isomorphic to `R[X]` as an `R[X]` module. -/
/-
**PolynomialModule.equivPolynomialSelf** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialModu
le`。
形式化陈述：equivPolynomialSelf : PolynomialModule R R ≃ₗ[R[X]] R[X] where toAddEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PolynomialModule R R` is isomorphic to `R[X]` as an `R[X]` module.
-/
def equivPolynomialSelf : PolynomialModule R R ≃ₗ[R[X]] R[X] where
  toAddEquiv := coeffAddEquiv.trans <| AddMonoidAlgebra.coeffAddEquiv.symm.trans
    (toFinsuppIso R).symm.toAddEquiv
  map_smul' r x := by
    dsimp
    induction x using induction_linear with
    | zero => simp
    | add _ _ hp hq => simp_all [smul_add, mul_add]
    | single n a =>
    ext i
    simp only [coeffAddEquiv_apply, AddMonoidAlgebra.coeffAddEquiv_symm_apply,
      toFinsuppIso_symm_apply, coeff_ofFinsupp, smul_single_apply, smul_eq_mul, coeff_single,
      AddMonoidAlgebra.ofCoeff_single, ofFinsupp_single]
    split_ifs with hn
    · rw [show i = (i - n) + n by lia, Polynomial.coeff_mul_monomial]
      simp
    · rw [Polynomial.coeff_mul, Finset.sum_eq_zero]
      simp [Polynomial.coeff_monomial]
      lia

/-- `PolynomialModule R S` is isomorphic to `S[X]` as an `R` module. -/
/-
**PolynomialModule.equivPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialModule`。
形式化陈述：equivPolynomial {S : Type*} [CommRing S] [Algebra R S] : PolynomialModule 
R S ≃ₗ[R] S[X] where toAddEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PolynomialModule R S` is isomorphic to `S[X]` as an `R` module.
-/
def equivPolynomial {S : Type*} [CommRing S] [Algebra R S] : PolynomialModule R S ≃ₗ[R] S[X] where
  toAddEquiv := coeffAddEquiv.trans <| AddMonoidAlgebra.coeffAddEquiv.symm.trans
    (toFinsuppIso _).symm.toAddEquiv
  map_smul' _ _ := rfl

@[simp]
/-
**PolynomialModule.equivPolynomialSelf_apply_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polyn
omialModule`。
形式化陈述：equivPolynomialSelf_apply_eq (p : PolynomialModule R R) : equivPolynomialS
elf p = equivPolynomial p
参数：p : PolynomialModule R R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivPolynomialSelf_apply_eq (p : PolynomialModule R R) :
    equivPolynomialSelf p = equivPolynomial p := rfl

@[simp]
/-
**PolynomialModule.equivPolynomial_single** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialM
odule`。
形式化陈述：equivPolynomial_single {S : Type*} [CommRing S] [Algebra R S] (n : Nat) (x
 : S) : equivPolynomial (single R n x) = monomial n x
参数：n : Nat；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivPolynomial_single {S : Type*} [CommRing S] [Algebra R S] (n : ℕ) (x : S) :
    equivPolynomial (single R n x) = monomial n x := rfl

@[simp]
/-
**PolynomialModule.equivPolynomial_symm_monomial** 是 Mathlib 中的一个引理，位于命名空间 `Poly
nomialModule`。
形式化陈述：equivPolynomial_symm_monomial {S : Type*} [CommRing S] [Algebra R S] (n : 
Nat) (x : S) : equivPolynomial.symm (monomial n x) = single R n x
参数：n : Nat；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivPolynomial_symm_monomial {S : Type*} [CommRing S] [Algebra R S] (n : ℕ) (x : S) :
    equivPolynomial.symm (monomial n x) = single R n x := rfl

@[simp]
/-
**PolynomialModule.equivPolynomial_symm_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
lModule`。
形式化陈述：equivPolynomial_symm_one {S : Type*} [CommRing S] [Algebra R S] : equivPol
ynomial.symm (1 : S[X]) = single R 0 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivPolynomial_symm_one {S : Type*} [CommRing S] [Algebra R S] :
    equivPolynomial.symm (1 : S[X]) = single R 0 1 := rfl

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']
variable [Module R M']

/-- Two `R`-linear maps from `PolynomialModule R M` which are equal
after pre-composition with every `lsingle R a` are equal. -/
@[ext high]
/-
**PolynomialModule.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：hom_ext {f g : PolynomialModule R M ->ₗ[R] M'} (h : forall a, f ∘ₗ lsingle
 R a = g ∘ₗ lsingle R a) : f = g
参数：h : forall a, f ∘ₗ lsingle R a = g ∘ₗ lsingle R a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolynomialModule.coeffLinearEquiv_symm_apply`：∀ (R : Type u_2) {M : Type
 u_3} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]
   (S : Type u_5) [inst_3 : CommSe…
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ

--- 原说明 ---
Two `R`-linear maps from `PolynomialModule R M` which are equal
after pre-composition with every `lsingle R a` are equal.
-/
theorem hom_ext {f g : PolynomialModule R M →ₗ[R] M'}
    (h : ∀ a, f ∘ₗ lsingle R a = g ∘ₗ lsingle R a) : f = g := by
  simpa [← DFunLike.coe_fn_eq, funext_iff, PolynomialModule.forall] using Finsupp.lhom_ext'
    (φ := f.comp (coeffLinearEquiv R R).symm.toLinearMap)
    (ψ := g.comp (coeffLinearEquiv R R (M := M)).symm.toLinearMap) h

/-- The image of a polynomial under a linear map. -/
/-
**PolynomialModule.map** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialModule`。
形式化陈述：map (f : M ->ₗ[R] M') : PolynomialModule R M ->ₗ[R] PolynomialModule R' M'
参数：f : M ->ₗ[R] M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a polynomial under a linear map.
-/
def map (f : M →ₗ[R] M') : PolynomialModule R M →ₗ[R] PolynomialModule R' M' :=
  (coeffLinearEquiv ..).symm.toLinearMap.comp <| (Finsupp.mapRange.linearMap f).comp <|
    (coeffLinearEquiv ..).toLinearMap

@[simp]
/-
**PolynomialModule.map_single** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：map_single (f : M ->ₗ[R] M') (i : Nat) (m : M) : map R' f (single R i m) =
 single R' i (f m)
参数：f : M ->ₗ[R] M'；i : Nat；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `PolynomialModule.coeffLinearEquiv_apply`：∀ (R : Type u_2) {M : Type u_3}
 [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (S
 : Type u_5) [inst_3 : CommSe…
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `PolynomialModule.coeffLinearEquiv_symm_apply`：∀ (R : Type u_2) {M : Type
 u_3} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]
   (S : Type u_5) [inst_3 : CommSe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_single (f : M →ₗ[R] M') (i : ℕ) (m : M) :
    map R' f (single R i m) = single R' i (f m) := by simp [map]

@[simp]
/-
**PolynomialModule.map_lsingle** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：map_lsingle (f : M ->ₗ[R] M') (i : Nat) (m : M) : map R' f (lsingle R i m)
 = lsingle R' i (f m)
参数：f : M ->ₗ[R] M'；i : Nat；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialModule.map_single`：map_single (f : M ->ₗ[R] M') (i : Nat) (m :
 M) : map R' f (single R i m) = single R' i (f m)
-/
theorem map_lsingle (f : M →ₗ[R] M') (i : ℕ) (m : M) :
    map R' f (lsingle R i m) = lsingle R' i (f m) :=
  map_single ..

variable [Algebra R R'] [IsScalarTower R R' M']
/-
**PolynomialModule.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：map_smul (f : M ->ₗ[R] M') (p : R[X]) (q : PolynomialModule R M) : map R' 
f (p • q) = p.map (algebraMap R R') • map R' f q
参数：f : M ->ₗ[R] M'；p : R[X]；q : PolynomialModule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PolynomialModule.induction_linear`：induction_linear {p : PolynomialModul
e R M -> Prop} (x : PolynomialModule R M) (zero : p 0) (add : forall x y : Polyn
omialModule R M, p x ->…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
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
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `PolynomialModule.monomial_smul_single`：monomial_smul_single (i : Nat) (r
 : R) (j : Nat) (m : M) : monomial i r • single R j m = single R (i + j) (r • m)
· 使用定理 `PolynomialModule.map_single`：map_single (f : M ->ₗ[R] M') (i : Nat) (m :
 M) : map R' f (single R i m) = single R' i (f m)
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
theorem map_smul (f : M →ₗ[R] M') (p : R[X]) (q : PolynomialModule R M) :
    map R' f (p • q) = p.map (algebraMap R R') • map R' f q := by
  induction q using induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add f g e₁ e₂ => rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  | single i m =>
    induction p using Polynomial.induction_on' with
    | add _ _ e₁ e₂ => rw [add_smul, map_add, e₁, e₂, Polynomial.map_add, add_smul]
    | monomial => rw [monomial_smul_single, map_single, Polynomial.map_monomial, map_single,
        monomial_smul_single, f.map_smul, algebraMap_smul]

set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluate a polynomial `p : PolynomialModule R M` at `r : R`. -/
@[simps! -isSimp]
/-
**PolynomialModule.eval** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialModule`。
形式化陈述：eval (r : R) : PolynomialModule R M ->ₗ[R] M where toFun p
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate a polynomial `p : PolynomialModule R M` at `r : R`.
-/
def eval (r : R) : PolynomialModule R M →ₗ[R] M where
  toFun p := p.coeff.sum fun i m => r ^ i • m
  map_add' _ _ := Finsupp.sum_add_index' (fun _ => smul_zero _) fun _ _ _ => smul_add _ _ _
  map_smul' s m := by
    refine (Finsupp.sum_smul_index' ?_).trans ?_
    · exact fun i => smul_zero _
    · simp_rw [RingHom.id_apply, Finsupp.smul_sum]
      congr
      ext i c
      rw [smul_comm]

@[simp]
/-
**PolynomialModule.eval_single** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：eval_single (r : R) (i : Nat) (m : M) : eval r (single R i m) = r ^ i • m
参数：r : R；i : Nat；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem eval_single (r : R) (i : ℕ) (m : M) : eval r (single R i m) = r ^ i • m :=
  Finsupp.sum_single_index (smul_zero _)

@[simp]
/-
**PolynomialModule.eval_lsingle** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：eval_lsingle (r : R) (i : Nat) (m : M) : eval r (lsingle R i m) = r ^ i • 
m
参数：r : R；i : Nat；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialModule.eval_single`：eval_single (r : R) (i : Nat) (m : M) : ev
al r (single R i m) = r ^ i • m
-/
theorem eval_lsingle (r : R) (i : ℕ) (m : M) : eval r (lsingle R i m) = r ^ i • m :=
  eval_single r i m

@[simp]
/-
**PolynomialModule.eval_smul** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：eval_smul (p : R[X]) (q : PolynomialModule R M) (r : R) : eval r (p • q) =
 p.eval r • eval r q
参数：p : R[X]；q : PolynomialModule R M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PolynomialModule.induction_linear`：induction_linear {p : PolynomialModul
e R M -> Prop} (x : PolynomialModule R M) (zero : p 0) (add : forall x y : Polyn
omialModule R M, p x ->…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
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
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PolynomialModule.monomial_smul_single`：monomial_smul_single (i : Nat) (r
 : R) (j : Nat) (m : M) : monomial i r • single R j m = single R (i + j) (r • m)
· 使用定理 `PolynomialModule.eval_single`：eval_single (r : R) (i : Nat) (m : M) : ev
al r (single R i m) = r ^ i • m
· 使用定理 `Polynomial.eval_monomial`：eval_monomial {n a} : (monomial n a).eval x = 
a * x ^ n
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 50 条，此处仅展示前 30 条）
-/
theorem eval_smul (p : R[X]) (q : PolynomialModule R M) (r : R) :
    eval r (p • q) = p.eval r • eval r q := by
  induction q using induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add f g e₁ e₂ => rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  | single i m =>
    induction p using Polynomial.induction_on' with
    | add _ _ e₁ e₂ => rw [add_smul, map_add, Polynomial.eval_add, e₁, e₂, add_smul]
    | monomial => simp only [monomial_smul_single, Polynomial.eval_monomial, eval_single]; module

@[simp]
/-
**PolynomialModule.eval_map** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：eval_map (f : M ->ₗ[R] M') (q : PolynomialModule R M) (r : R) : eval (alge
braMap R R' r) (map R' f q) = f (eval r q)
参数：f : M ->ₗ[R] M'；q : PolynomialModule R M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PolynomialModule.induction_linear`：induction_linear {p : PolynomialModul
e R M -> Prop} (x : PolynomialModule R M) (zero : p 0) (add : forall x y : Polyn
omialModule R M, p x ->…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PolynomialModule.map_single`：map_single (f : M ->ₗ[R] M') (i : Nat) (m :
 M) : map R' f (single R i m) = single R' i (f m)
· 使用定理 `PolynomialModule.eval_single`：eval_single (r : R) (i : Nat) (m : M) : ev
al r (single R i m) = r ^ i • m
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `algebraMap.coe_mul`：coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b
· 使用定理 `algebraMap.coe_pow`：coe_pow (a : R) (n : Nat) : (↑(a ^ n : R) : A) = (a 
: A) ^ n
· 使用定理 `algebraMap.coe_one`：coe_one : (↑(1 : R) : A) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 48 条，此处仅展示前 30 条）
-/
theorem eval_map (f : M →ₗ[R] M') (q : PolynomialModule R M) (r : R) :
    eval (algebraMap R R' r) (map R' f q) = f (eval r q) := by
  induction q using induction_linear with
  | zero => simp_rw [map_zero]
  | add f g e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m => simp only [map_single, eval_single, f.map_smul]; module

@[simp]
/-
**PolynomialModule.eval_map'** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：eval_map' (f : M ->ₗ[R] M) (q : PolynomialModule R M) (r : R) : eval r (ma
p R f q) = f (eval r q)
参数：f : M ->ₗ[R] M；q : PolynomialModule R M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialModule.eval_map`：eval_map (f : M ->ₗ[R] M') (q : PolynomialMod
ule R M) (r : R) : eval (algebraMap R R' r) (map R' f q) = f (eval r q)
-/
theorem eval_map' (f : M →ₗ[R] M) (q : PolynomialModule R M) (r : R) :
    eval r (map R f q) = f (eval r q) :=
  eval_map R f q r

@[simp]
/-
**PolynomialModule.aeval_equivPolynomial** 是 Mathlib 中的一个引理，位于命名空间 `PolynomialMo
dule`。
形式化陈述：aeval_equivPolynomial {S : Type*} [CommRing S] [Algebra S R] (f : Polynomi
alModule S S) (x : R) : aeval x (equivPolynomial f) = eval x (map R (Algebra.lin
earMap S R) f)
参数：f : PolynomialModule S S；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PolynomialModule.induction_linear`：induction_linear {p : PolynomialModul
e R M -> Prop} (x : PolynomialModule R M) (zero : p 0) (add : forall x y : Polyn
omialModule R M, p x ->…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `PolynomialModule.equivPolynomial_single`：equivPolynomial_single {S : Typ
e*} [CommRing S] [Algebra R S] (n : Nat) (x : S) : equivPolynomial (single R n x
) = monomial n x
· 使用定理 `Polynomial.aeval_monomial`：aeval_monomial {n : Nat} {r : R} : aeval x (m
onomial n r) = algebraMap _ _ r * x ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PolynomialModule.map_single`：map_single (f : M ->ₗ[R] M') (i : Nat) (m :
 M) : map R' f (single R i m) = single R' i (f m)
· 使用定理 `Algebra.linearMap_apply`：linearMap_apply (r : R) : Algebra.linearMap R A
 r = algebraMap R A r
· 使用定理 `PolynomialModule.eval_single`：eval_single (r : R) (i : Nat) (m : M) : ev
al r (single R i m) = r ^ i • m
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
-/
lemma aeval_equivPolynomial {S : Type*} [CommRing S] [Algebra S R]
    (f : PolynomialModule S S) (x : R) :
    aeval x (equivPolynomial f) = eval x (map R (Algebra.linearMap S R) f) := by
  induction f using induction_linear with
  | zero => simp
  | add f g e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m => rw [equivPolynomial_single, aeval_monomial, mul_comm, map_single,
      Algebra.linearMap_apply, eval_single, smul_eq_mul]

/-- `comp p q` is the composition of `p : R[X]` and `q : M[X]` as `q(p(x))`. -/
@[simps!]
/-
**PolynomialModule.comp** 是 Mathlib 中的一个定义，位于命名空间 `PolynomialModule`。
形式化陈述：comp (p : R[X]) : PolynomialModule R M ->ₗ[R] PolynomialModule R M
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`comp p q` is the composition of `p : R[X]` and `q : M[X]` as `q(p(x))`.
-/
def comp (p : R[X]) : PolynomialModule R M →ₗ[R] PolynomialModule R M :=
  LinearMap.comp ((eval p).restrictScalars R) (map R[X] (lsingle R 0))
/-
**PolynomialModule.comp_single** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：comp_single (p : R[X]) (i : Nat) (m : M) : comp p (single R i m) = p ^ i •
 single R 0 m
参数：p : R[X]；i : Nat；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolynomialModule.comp_apply`：∀ {R : Type u_2} {M : Type u_3} [inst : Com
mRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Polynomia
l R) (x : Polynom…
· 使用定理 `PolynomialModule.map_single`：map_single (f : M ->ₗ[R] M') (i : Nat) (m :
 M) : map R' f (single R i m) = single R' i (f m)
· 使用定理 `PolynomialModule.eval_single`：eval_single (r : R) (i : Nat) (m : M) : ev
al r (single R i m) = r ^ i • m
-/
theorem comp_single (p : R[X]) (i : ℕ) (m : M) : comp p (single R i m) = p ^ i • single R 0 m := by
  rw [comp_apply, map_single, eval_single]
  rfl
/-
**PolynomialModule.comp_eval** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：comp_eval (p : R[X]) (q : PolynomialModule R M) (r : R) : eval r (comp p q
) = eval (p.eval r) q
参数：p : R[X]；q : PolynomialModule R M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用引理 `PolynomialModule.induction_linear`：induction_linear {p : PolynomialModul
e R M -> Prop} (x : PolynomialModule R M) (zero : p 0) (add : forall x y : Polyn
omialModule R M, p x ->…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PolynomialModule.comp_single`：comp_single (p : R[X]) (i : Nat) (m : M) :
 comp p (single R i m) = p ^ i • single R 0 m
· 使用定理 `PolynomialModule.eval_single`：eval_single (r : R) (i : Nat) (m : M) : ev
al r (single R i m) = r ^ i • m
· 使用定理 `PolynomialModule.eval_smul`：eval_smul (p : R[X]) (q : PolynomialModule R
 M) (r : R) : eval r (p • q) = p.eval r • eval r q
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 48 条，此处仅展示前 30 条）
-/
theorem comp_eval (p : R[X]) (q : PolynomialModule R M) (r : R) :
    eval r (comp p q) = eval (p.eval r) q := by
  rw [← LinearMap.comp_apply]
  induction q using induction_linear with
  | zero => simp_rw [map_zero]
  | add _ _ e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m =>
    rw [LinearMap.comp_apply, comp_single, eval_single, eval_smul, eval_single, eval_pow]
    module
/-
**PolynomialModule.comp_smul** 是 Mathlib 中的一个定理，位于命名空间 `PolynomialModule`。
形式化陈述：comp_smul (p p' : R[X]) (q : PolynomialModule R M) : comp p (p' • q) = p'.
comp p • comp p q
参数：p p' : R[X]；q : PolynomialModule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolynomialModule.comp_apply`：∀ {R : Type u_2} {M : Type u_3} [inst : Com
mRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Polynomia
l R) (x : Polynom…
· 使用定理 `PolynomialModule.map_smul`：map_smul (f : M ->ₗ[R] M') (p : R[X]) (q : Po
lynomialModule R M) : map R' f (p • q) = p.map (algebraMap R R') • map R' f q
· 使用定理 `PolynomialModule.eval_smul`：eval_smul (p : R[X]) (q : PolynomialModule R
 M) (r : R) : eval r (p • q) = p.eval r • eval r q
· 使用定理 `Polynomial.comp.eq_1`：∀ {R : Type u} [inst : Semiring R] (p q : Polynomi
al R), p.comp q = Polynomial.eval₂ Polynomial.C q p
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
-/
theorem comp_smul (p p' : R[X]) (q : PolynomialModule R M) :
    comp p (p' • q) = p'.comp p • comp p q := by
  rw [comp_apply, map_smul, eval_smul, Polynomial.comp, Polynomial.eval_map, comp_apply]
  rfl

end PolynomialModule

