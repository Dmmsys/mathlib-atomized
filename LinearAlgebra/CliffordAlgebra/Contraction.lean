/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Contraction in Clifford Algebras

This file contains some of the results from [grinberg_clifford_2016].
The key result is `CliffordAlgebra.equivExterior`.

## Main definitions

* `CliffordAlgebra.contractLeft`: contract a multivector by a `Module.Dual R M` on the left.
* `CliffordAlgebra.contractRight`: contract a multivector by a `Module.Dual R M` on the right.
* `CliffordAlgebra.changeForm`: convert between two algebras of different quadratic forms, sending
  vectors to vectors. The difference of the quadratic forms must be a bilinear form.
* `CliffordAlgebra.equivExterior`: in characteristic not-two, the `CliffordAlgebra Q` is
  isomorphic as a module to the exterior algebra.

## Implementation notes

This file somewhat follows [grinberg_clifford_2016], although we are missing some of the induction
principles needed to prove many of the results. Here, we avoid the quotient-based approach described
in [grinberg_clifford_2016], instead directly constructing our objects using the universal
property.

Note that [grinberg_clifford_2016] concludes that its contents are not novel, and are in fact just
a rehash of parts of [bourbaki2007]; we should at some point consider swapping our references to
refer to the latter.

Within this file, we use the local notation
* `x ⌊ d` for `contractRight x d`
* `d ⌋ x` for `contractLeft d x`

-/

@[expose] public section

open LinearMap (BilinMap BilinForm)

universe u1 u2 u3

variable {R : Type u1} [CommRing R]
variable {M : Type u2} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

namespace CliffordAlgebra

section contractLeft

variable (d d' : Module.Dual R M)

set_option backward.isDefEq.respectTransparency false in -- This is needed below
/-- Auxiliary construction for `CliffordAlgebra.contractLeft` -/
@[simps!]
/-
**CliffordAlgebra.contractLeftAux** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：contractLeftAux (d : Module.Dual R M) : M ->ₗ[R] CliffordAlgebra Q × Cliff
ordAlgebra Q ->ₗ[R] CliffordAlgebra Q
参数：d : Module.Dual R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction for `CliffordAlgebra.contractLeft`
-/
def contractLeftAux (d : Module.Dual R M) :
    M →ₗ[R] CliffordAlgebra Q × CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  haveI v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  d.smulRight (LinearMap.fst _ (CliffordAlgebra Q) (CliffordAlgebra Q)) -
    v_mul.compl₂ (LinearMap.snd _ (CliffordAlgebra Q) _)
/-
**CliffordAlgebra.contractLeftAux_contractLeftAux** 是 Mathlib 中的一个定理，位于命名空间 `Cli
ffordAlgebra`。
形式化陈述：contractLeftAux_contractLeftAux (v : M) (x : CliffordAlgebra Q) (fx : Clif
fordAlgebra Q) : contractLeftAux Q d v (ι Q v * x, contractLeftAux Q d v (x, fx)
) = Q v • fx
参数：v : M；x : CliffordAlgebra Q；fx : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CliffordAlgebra.contractLeftAux_apply_apply`：∀ {R : Type u1} [inst : Com
mRing R] {M : Type u2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   
(Q : QuadraticForm R M) (d : Modu…
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `CliffordAlgebra.ι_sq_scalar`：ι_sq_scalar (m : M) : ι Q m * ι Q m = algeb
raMap R _ (Q m)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem contractLeftAux_contractLeftAux (v : M) (x : CliffordAlgebra Q) (fx : CliffordAlgebra Q) :
    contractLeftAux Q d v (ι Q v * x, contractLeftAux Q d v (x, fx)) = Q v • fx := by
  simp only [contractLeftAux_apply_apply]
  rw [mul_sub, ← mul_assoc, ι_sq_scalar, ← Algebra.smul_def, ← sub_add, mul_smul_comm, sub_self,
    zero_add]

variable {Q}

set_option backward.defeqAttrib.useBackward true in
/-- Contract an element of the Clifford algebra with an element `d : Module.Dual R M` from the left.

Note that $v ⌋ x$ is spelt `contractLeft (Q.associated v) x`.

This includes [grinberg_clifford_2016] Theorem 10.75 -/
/-
**CliffordAlgebra.contractLeft** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：contractLeft : Module.Dual R M ->ₗ[R] CliffordAlgebra Q ->ₗ[R] CliffordAlg
ebra Q where toFun d
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.contractLeftAux_contractLeftAux`：contractLeftAux_contrac
tLeftAux (v : M) (x : CliffordAlgebra Q) (fx : CliffordAlgebra Q) : contractLeft
Aux Q d v (ι Q v * x, contractLeftAux…

--- 原说明 ---
Contract an element of the Clifford algebra with an element `d : Module.Dual R M
` from the left.

Note that $v ⌋ x$ is spelt `contractLeft (Q.associated v) x`.

This includes [grinberg_clifford_2016] Theorem 10.75
-/
def contractLeft : Module.Dual R M →ₗ[R] CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q where
  toFun d := foldr' Q (contractLeftAux Q d) (contractLeftAux_contractLeftAux Q d) 0
  map_add' d₁ d₂ :=
    LinearMap.ext fun x => by
      rw [LinearMap.add_apply]
      induction x using CliffordAlgebra.left_induction with
      | algebraMap => simp_rw [foldr'_algebraMap, smul_zero, zero_add]
      | add _ _ hx hy => rw [map_add, map_add, map_add, add_add_add_comm, hx, hy]
      | ι_mul _ _ hx =>
        rw [foldr'_ι_mul, foldr'_ι_mul, foldr'_ι_mul, hx]
        dsimp only [contractLeftAux_apply_apply]
        rw [sub_add_sub_comm, mul_add, LinearMap.add_apply, add_smul]
  map_smul' c d :=
    LinearMap.ext fun x => by
      rw [LinearMap.smul_apply, RingHom.id_apply]
      induction x using CliffordAlgebra.left_induction with
      | algebraMap => simp_rw [foldr'_algebraMap, smul_zero]
      | add _ _ hx hy => rw [map_add, map_add, smul_add, hx, hy]
      | ι_mul _ _ hx =>
        rw [foldr'_ι_mul, foldr'_ι_mul, hx]
        dsimp only [contractLeftAux_apply_apply]
        rw [LinearMap.smul_apply, smul_assoc, mul_smul_comm, smul_sub]

/-- Contract an element of the Clifford algebra with an element `d : Module.Dual R M` from the
right.

Note that $x ⌊ v$ is spelt `contractRight x (Q.associated v)`.

This includes [grinberg_clifford_2016] Theorem 16.75 -/
/-
**CliffordAlgebra.contractRight** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：contractRight : CliffordAlgebra Q ->ₗ[R] Module.Dual R M ->ₗ[R] CliffordAl
gebra Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Contract an element of the Clifford algebra with an element `d : Module.Dual R M
` from the
right.

Note that $x ⌊ v$ is spelt `contractRight x (Q.associated v)`.

This includes [grinberg_clifford_2016] Theorem 16.75
-/
def contractRight : CliffordAlgebra Q →ₗ[R] Module.Dual R M →ₗ[R] CliffordAlgebra Q :=
  LinearMap.flip (LinearMap.compl₂ (LinearMap.compr₂ contractLeft reverse) reverse)
/-
**CliffordAlgebra.contractRight_eq** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：contractRight_eq (x : CliffordAlgebra Q) : contractRight (Q
参数：x : CliffordAlgebra Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
-/
theorem contractRight_eq (x : CliffordAlgebra Q) :
    contractRight (Q := Q) x d = reverse (contractLeft (R := R) (M := M) d <| reverse x) :=
  rfl

local infixl:70 "⌋" => contractLeft (R := R) (M := M)

local infixl:70 "⌊" => contractRight (R := R) (M := M) (Q := Q)

/-- This is [grinberg_clifford_2016] Theorem 6 -/
/-
**CliffordAlgebra.contractLeft_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is [grinberg_clifford_2016] Theorem 6
-/
theorem contractLeft_ι_mul (a : M) (b : CliffordAlgebra Q) :
    d⌋(ι Q a * b) = d a • b - ι Q a * (d⌋b) := by
-- Porting note: Lean cannot figure out anymore the third argument
  refine foldr'_ι_mul _ _ ?_ _ _ _
  exact fun m x fx ↦ contractLeftAux_contractLeftAux Q d m x fx

/-- This is [grinberg_clifford_2016] Theorem 12 -/
/-
**CliffordAlgebra.contractRight_mul_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is [grinberg_clifford_2016] Theorem 12
-/
theorem contractRight_mul_ι (a : M) (b : CliffordAlgebra Q) :
    b * ι Q a⌊d = d a • b - b⌊d * ι Q a := by
  rw [contractRight_eq, reverse.map_mul, reverse_ι, contractLeft_ι_mul, map_sub, map_smul,
    reverse_reverse, reverse.map_mul, reverse_ι, contractRight_eq]
/-
**CliffordAlgebra.contractLeft_algebraMap_mul** 是 Mathlib 中的一个定理，位于命名空间 `Cliffor
dAlgebra`。
形式化陈述：contractLeft_algebraMap_mul (r : R) (b : CliffordAlgebra Q) : d⌋(algebraMa
p _ _ r * b) = algebraMap _ _ r * (d⌋b)
参数：r : R；b : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
theorem contractLeft_algebraMap_mul (r : R) (b : CliffordAlgebra Q) :
    d⌋(algebraMap _ _ r * b) = algebraMap _ _ r * (d⌋b) := by
  rw [← Algebra.smul_def, map_smul, Algebra.smul_def]
/-
**CliffordAlgebra.contractLeft_mul_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Cliffor
dAlgebra`。
形式化陈述：contractLeft_mul_algebraMap (a : CliffordAlgebra Q) (r : R) : d⌋(a * algeb
raMap _ _ r) = d⌋a * algebraMap _ _ r
参数：a : CliffordAlgebra Q；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `CliffordAlgebra.contractLeft_algebraMap_mul`：contractLeft_algebraMap_mul
 (r : R) (b : CliffordAlgebra Q) : d⌋(algebraMap _ _ r * b) = algebraMap _ _ r *
 (d⌋b)
-/
theorem contractLeft_mul_algebraMap (a : CliffordAlgebra Q) (r : R) :
    d⌋(a * algebraMap _ _ r) = d⌋a * algebraMap _ _ r := by
  rw [← Algebra.commutes, contractLeft_algebraMap_mul, Algebra.commutes]
/-
**CliffordAlgebra.contractRight_algebraMap_mul** 是 Mathlib 中的一个定理，位于命名空间 `Cliffo
rdAlgebra`。
形式化陈述：contractRight_algebraMap_mul (r : R) (b : CliffordAlgebra Q) : algebraMap 
_ _ r * b⌊d = algebraMap _ _ r * (b⌊d)
参数：r : R；b : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `LinearMap.map_smul₂`：map_smul₂ (f : M₂ ->ₗ[R] N₂ ->ₛₗ[σ₁₂] P₂) (r : R) (
x y) : f (r • x) y = r • f x y
-/
theorem contractRight_algebraMap_mul (r : R) (b : CliffordAlgebra Q) :
    algebraMap _ _ r * b⌊d = algebraMap _ _ r * (b⌊d) := by
  rw [← Algebra.smul_def, LinearMap.map_smul₂, Algebra.smul_def]
/-
**CliffordAlgebra.contractRight_mul_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Cliffo
rdAlgebra`。
形式化陈述：contractRight_mul_algebraMap (a : CliffordAlgebra Q) (r : R) : a * algebra
Map _ _ r⌊d = a⌊d * algebraMap _ _ r
参数：a : CliffordAlgebra Q；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `CliffordAlgebra.contractRight_algebraMap_mul`：contractRight_algebraMap_m
ul (r : R) (b : CliffordAlgebra Q) : algebraMap _ _ r * b⌊d = algebraMap _ _ r *
 (b⌊d)
-/
theorem contractRight_mul_algebraMap (a : CliffordAlgebra Q) (r : R) :
    a * algebraMap _ _ r⌊d = a⌊d * algebraMap _ _ r := by
  rw [← Algebra.commutes, contractRight_algebraMap_mul, Algebra.commutes]

variable (Q)

@[simp]
/-
**CliffordAlgebra.contractLeft_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem contractLeft_ι (x : M) : d⌋ι Q x = algebraMap R _ (d x) := by
-- Porting note: Lean cannot figure out anymore the third argument
  refine (foldr'_ι _ _ ?_ _ _).trans <| by
    simp_rw [contractLeftAux_apply_apply, mul_zero, sub_zero,
      Algebra.algebraMap_eq_smul_one]
  exact fun m x fx ↦ contractLeftAux_contractLeftAux Q d m x fx

@[simp]
/-
**CliffordAlgebra.contractRight_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem contractRight_ι (x : M) : ι Q x⌊d = algebraMap R _ (d x) := by
  rw [contractRight_eq, reverse_ι, contractLeft_ι, reverse.commutes]

@[simp]
/-
**CliffordAlgebra.contractLeft_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlg
ebra`。
形式化陈述：contractLeft_algebraMap (r : R) : d⌋algebraMap R (CliffordAlgebra Q) r = 0
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CliffordAlgebra.contractLeftAux_contractLeftAux`：contractLeftAux_contrac
tLeftAux (v : M) (x : CliffordAlgebra Q) (fx : CliffordAlgebra Q) : contractLeft
Aux Q d v (ι Q v * x, contractLeftAux…
· 使用定理 `CliffordAlgebra.foldr'_algebraMap`：∀ {R : Type u_1} {M : Type u_2} {N : 
Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup N
]   [inst_3 : _root_.Mo…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem contractLeft_algebraMap (r : R) : d⌋algebraMap R (CliffordAlgebra Q) r = 0 := by
-- Porting note: Lean cannot figure out anymore the third argument
  refine (foldr'_algebraMap _ _ ?_ _ _).trans <| smul_zero _
  exact fun m x fx ↦ contractLeftAux_contractLeftAux Q d m x fx

@[simp]
/-
**CliffordAlgebra.contractRight_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAl
gebra`。
形式化陈述：contractRight_algebraMap (r : R) : algebraMap R (CliffordAlgebra Q) r⌊d = 
0
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.contractRight_eq`：contractRight_eq (x : CliffordAlgebra 
Q) : contractRight (Q
· 使用定理 `CliffordAlgebra.reverse.commutes`：∀ {R : Type u_1} [inst : CommRing R] {
M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quad
raticForm R M} (r : R)…
· 使用定理 `CliffordAlgebra.contractLeft_algebraMap`：contractLeft_algebraMap (r : R)
 : d⌋algebraMap R (CliffordAlgebra Q) r = 0
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
-/
theorem contractRight_algebraMap (r : R) : algebraMap R (CliffordAlgebra Q) r⌊d = 0 := by
  rw [contractRight_eq, reverse.commutes, contractLeft_algebraMap, map_zero]

@[simp]
/-
**CliffordAlgebra.contractLeft_one** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：contractLeft_one : d⌋(1 : CliffordAlgebra Q) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `CliffordAlgebra.contractLeft_algebraMap`：contractLeft_algebraMap (r : R)
 : d⌋algebraMap R (CliffordAlgebra Q) r = 0
-/
theorem contractLeft_one : d⌋(1 : CliffordAlgebra Q) = 0 := by
  simpa only [map_one] using contractLeft_algebraMap Q d 1

@[simp]
/-
**CliffordAlgebra.contractRight_one** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：contractRight_one : (1 : CliffordAlgebra Q)⌊d = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `CliffordAlgebra.contractRight_algebraMap`：contractRight_algebraMap (r : 
R) : algebraMap R (CliffordAlgebra Q) r⌊d = 0
-/
theorem contractRight_one : (1 : CliffordAlgebra Q)⌊d = 0 := by
  simpa only [map_one] using contractRight_algebraMap Q d 1

variable {Q}

/-- This is [grinberg_clifford_2016] Theorem 7 -/
/-
**CliffordAlgebra.contractLeft_contractLeft** 是 Mathlib 中的一个定理，位于命名空间 `CliffordA
lgebra`。
形式化陈述：contractLeft_contractLeft (x : CliffordAlgebra Q) : d⌋(d⌋x) = 0
参数：x : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.left_induction`：left_induction {P : CliffordAlgebra Q ->
 Prop} (algebraMap : forall r : R, P (algebraMap _ _ r)) (add : forall x y, P x 
-> P y -> P (x + y))…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.contractLeft_algebraMap`：contractLeft_algebraMap (r : R)
 : d⌋algebraMap R (CliffordAlgebra Q) r = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CliffordAlgebra.contractLeft_ι_mul`：contractLeft_ι_mul (a : M) (b : Clif
fordAlgebra Q) : d⌋(ι Q a * b) = d a • b - ι Q a * (d⌋b)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
This is [grinberg_clifford_2016] Theorem 7
-/
theorem contractLeft_contractLeft (x : CliffordAlgebra Q) : d⌋(d⌋x) = 0 := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [contractLeft_algebraMap, map_zero]
  | add _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | ι_mul _ _ hx =>
    rw [contractLeft_ι_mul, map_sub, contractLeft_ι_mul, hx, map_smul, mul_zero, sub_zero, sub_self]

/-- This is [grinberg_clifford_2016] Theorem 13 -/
/-
**CliffordAlgebra.contractRight_contractRight** 是 Mathlib 中的一个定理，位于命名空间 `Cliffor
dAlgebra`。
形式化陈述：contractRight_contractRight (x : CliffordAlgebra Q) : x⌊d⌊d = 0
参数：x : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.contractRight_eq`：contractRight_eq (x : CliffordAlgebra 
Q) : contractRight (Q
· 使用定理 `CliffordAlgebra.reverse_reverse`：reverse_reverse : forall a : CliffordAl
gebra Q, reverse (reverse a) = a
· 使用定理 `CliffordAlgebra.contractLeft_contractLeft`：contractLeft_contractLeft (x 
: CliffordAlgebra Q) : d⌋(d⌋x) = 0
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

--- 原说明 ---
This is [grinberg_clifford_2016] Theorem 13
-/
theorem contractRight_contractRight (x : CliffordAlgebra Q) : x⌊d⌊d = 0 := by
  rw [contractRight_eq, contractRight_eq, reverse_reverse, contractLeft_contractLeft, map_zero]

/-- This is [grinberg_clifford_2016] Theorem 8 -/
/-
**CliffordAlgebra.contractLeft_comm** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：contractLeft_comm (x : CliffordAlgebra Q) : d⌋(d'⌋x) = -(d'⌋(d⌋x))
参数：x : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.left_induction`：left_induction {P : CliffordAlgebra Q ->
 Prop} (algebraMap : forall r : R, P (algebraMap _ _ r)) (add : forall x y, P x 
-> P y -> P (x + y))…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.contractLeft_algebraMap`：contractLeft_algebraMap (r : R)
 : d⌋algebraMap R (CliffordAlgebra Q) r = 0
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `CliffordAlgebra.contractLeft_ι_mul`：contractLeft_ι_mul (a : M) (b : Clif
fordAlgebra Q) : d⌋(ι Q a * b) = d a • b - ι Q a * (d⌋b)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_sub_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b c
 : α), a - (b - c) = a + c - b
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b

--- 原说明 ---
This is [grinberg_clifford_2016] Theorem 8
-/
theorem contractLeft_comm (x : CliffordAlgebra Q) : d⌋(d'⌋x) = -(d'⌋(d⌋x)) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [contractLeft_algebraMap, map_zero, neg_zero]
  | add _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy, neg_add]
  | ι_mul _ _ hx =>
    simp only [contractLeft_ι_mul, map_sub, map_smul]
    rw [neg_sub, sub_sub_eq_add_sub, hx, mul_neg, ← sub_eq_add_neg]

/-- This is [grinberg_clifford_2016] Theorem 14 -/
/-
**CliffordAlgebra.contractRight_comm** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`
。
形式化陈述：contractRight_comm (x : CliffordAlgebra Q) : x⌊d⌊d' = -(x⌊d'⌊d)
参数：x : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.contractRight_eq`：contractRight_eq (x : CliffordAlgebra 
Q) : contractRight (Q
· 使用定理 `CliffordAlgebra.reverse_reverse`：reverse_reverse : forall a : CliffordAl
gebra Q, reverse (reverse a) = a
· 使用定理 `CliffordAlgebra.contractLeft_comm`：contractLeft_comm (x : CliffordAlgebr
a Q) : d⌋(d'⌋x) = -(d'⌋(d⌋x))
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…

--- 原说明 ---
This is [grinberg_clifford_2016] Theorem 14
-/
theorem contractRight_comm (x : CliffordAlgebra Q) : x⌊d⌊d' = -(x⌊d'⌊d) := by
  rw [contractRight_eq, contractRight_eq, contractRight_eq, contractRight_eq, reverse_reverse,
    reverse_reverse, contractLeft_comm, map_neg]

/- TODO:
lemma contractRight_contractLeft (x : CliffordAlgebra Q) : (d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d') :=
-/
end contractLeft

local infixl:70 "⌋" => contractLeft

local infixl:70 "⌊" => contractRight

/-- Auxiliary construction for `CliffordAlgebra.changeForm` -/
@[simps!]
/-
**CliffordAlgebra.changeFormAux** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：changeFormAux (B : BilinForm R M) : M ->ₗ[R] CliffordAlgebra Q ->ₗ[R] Clif
fordAlgebra Q
参数：B : BilinForm R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction for `CliffordAlgebra.changeForm`
-/
def changeFormAux (B : BilinForm R M) : M →ₗ[R] CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  haveI v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  v_mul - contractLeft ∘ₗ B
/-
**CliffordAlgebra.changeFormAux_changeFormAux** 是 Mathlib 中的一个定理，位于命名空间 `Cliffor
dAlgebra`。
形式化陈述：changeFormAux_changeFormAux (B : BilinForm R M) (v : M) (x : CliffordAlgeb
ra Q) : changeFormAux Q B v (changeFormAux Q B v x) = (Q v - B v v) • x
参数：B : BilinForm R M；v : M；x : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CliffordAlgebra.changeFormAux_apply_apply`：∀ {R : Type u1} [inst : CommR
ing R] {M : Type u2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (Q
 : QuadraticForm R M) (B : Line…
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `CliffordAlgebra.ι_sq_scalar`：ι_sq_scalar (m : M) : ι Q m * ι Q m = algeb
raMap R _ (Q m)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.contractLeft_ι_mul`：contractLeft_ι_mul (a : M) (b : Clif
fordAlgebra Q) : d⌋(ι Q a * b) = d a • b - ι Q a * (d⌋b)
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `sub_sub_sub_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a - b - (c - d) = a - c - (b - d)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `CliffordAlgebra.contractLeft_contractLeft`：contractLeft_contractLeft (x 
: CliffordAlgebra Q) : d⌋(d⌋x) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
-/
theorem changeFormAux_changeFormAux (B : BilinForm R M) (v : M) (x : CliffordAlgebra Q) :
    changeFormAux Q B v (changeFormAux Q B v x) = (Q v - B v v) • x := by
  simp only [changeFormAux_apply_apply]
  rw [mul_sub, ← mul_assoc, ι_sq_scalar, map_sub, contractLeft_ι_mul, ← sub_add, sub_sub_sub_comm,
    ← Algebra.smul_def, sub_self, sub_zero, contractLeft_contractLeft, add_zero, sub_smul]

variable {Q}
variable {Q' Q'' : QuadraticForm R M} {B B' : BilinForm R M}

/-- Convert between two algebras of different quadratic forms, sending vectors to vectors, scalars
to scalars, and adjusting products by a contraction term.

This is $\lambda_B$ from [bourbaki2007] §9 Lemma 2. -/
/-
**CliffordAlgebra.changeForm** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：changeForm (h : B.toQuadraticMap = Q' - Q) : CliffordAlgebra Q ->ₗ[R] Clif
fordAlgebra Q'
参数：h : B.toQuadraticMap = Q' - Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert between two algebras of different quadratic forms, sending vectors to ve
ctors, scalars
to scalars, and adjusting products by a contraction term.

This is $\lambda_B$ from [bourbaki2007] §9 Lemma 2.
-/
def changeForm (h : B.toQuadraticMap = Q' - Q) : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q' :=
  foldr Q (changeFormAux Q' B)
    (fun m x =>
      (changeFormAux_changeFormAux Q' B m x).trans <| by
        rw [← BilinMap.toQuadraticMap_apply, h, sub_apply, sub_sub_cancel])
    1

/-- Auxiliary lemma used as an argument to `CliffordAlgebra.changeForm` -/
/-
**CliffordAlgebra.changeForm.zero_proof** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
ra.changeForm`。
形式化陈述：∀ {R : Type u1} [inst : CommRing R] {M : Type u2} [inst_1 : AddCommGroup M
] [inst_2 : _root_.Module R M]   {Q : QuadraticForm R M}, LinearMap.BilinMap.toQ
uadraticMap 0 = Q - Q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
Auxiliary lemma used as an argument to `CliffordAlgebra.changeForm`
-/
theorem changeForm.zero_proof : (0 : BilinForm R M).toQuadraticMap = Q - Q :=
  (sub_self _).symm

variable (h : B.toQuadraticMap = Q' - Q) (h' : B'.toQuadraticMap = Q'' - Q')

include h h' in
/-- Auxiliary lemma used as an argument to `CliffordAlgebra.changeForm` -/
/-
**CliffordAlgebra.changeForm.add_proof** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebr
a.changeForm`。
形式化陈述：∀ {R : Type u1} [inst : CommRing R] {M : Type u2} [inst_1 : AddCommGroup M
] [inst_2 : _root_.Module R M]   {Q Q' Q'' : QuadraticForm R M} {B B' : LinearMa
p.BilinForm R M},   LinearMap.BilinMap.toQuadraticMap B = Q' - Q →     LinearMap
.BilinMap.toQuadraticMap B' = Q'' - Q' → LinearMap.BilinMap.toQuadraticMap (B + 
B') = Q'' - Q
参数：B + B'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `sub_add_sub_cancel'`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G
), a - b + (c - a) = c - b

--- 原说明 ---
Auxiliary lemma used as an argument to `CliffordAlgebra.changeForm`
-/
theorem changeForm.add_proof : (B + B').toQuadraticMap = Q'' - Q :=
  (congr_arg₂ (· + ·) h h').trans <| sub_add_sub_cancel' _ _ _

include h in
/-- Auxiliary lemma used as an argument to `CliffordAlgebra.changeForm` -/
/-
**CliffordAlgebra.changeForm.neg_proof** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebr
a.changeForm`。
形式化陈述：∀ {R : Type u1} [inst : CommRing R] {M : Type u2} [inst_1 : AddCommGroup M
] [inst_2 : _root_.Module R M]   {Q Q' : QuadraticForm R M} {B : LinearMap.Bilin
Form R M},   LinearMap.BilinMap.toQuadraticMap B = Q' - Q → LinearMap.BilinMap.t
oQuadraticMap (-B) = Q - Q'
参数：-B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a

--- 原说明 ---
Auxiliary lemma used as an argument to `CliffordAlgebra.changeForm`
-/
theorem changeForm.neg_proof : (-B).toQuadraticMap = Q - Q' :=
  (congr_arg Neg.neg h).trans <| neg_sub _ _
/-
**CliffordAlgebra.changeForm.associated_neg_proof** 是 Mathlib 中的一个定理，位于命名空间 `Cli
ffordAlgebra.changeForm`。
形式化陈述：∀ {R : Type u1} [inst : CommRing R] {M : Type u2} [inst_1 : AddCommGroup M
] [inst_2 : _root_.Module R M]   {Q : QuadraticForm R M} [inst_3 : Invertible 2]
, (QuadraticMap.associated (-Q)).toQuadraticMap = 0 - Q
参数：QuadraticMap.associated (-Q)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `QuadraticMap.toQuadraticMap_associated`：toQuadraticMap_associated : (ass
ociatedHom S Q).toQuadraticMap = Q
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem changeForm.associated_neg_proof [Invertible (2 : R)] :
    (QuadraticMap.associated (R := R) (M := M) (-Q)).toQuadraticMap = 0 - Q := by
  simp [QuadraticMap.toQuadraticMap_associated]

@[simp]
/-
**CliffordAlgebra.changeForm_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
ra`。
形式化陈述：changeForm_algebraMap (r : R) : changeForm h (algebraMap R _ r) = algebraM
ap R _ r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CliffordAlgebra.foldr_algebraMap`：foldr_algebraMap (f : M ->ₗ[R] N ->ₗ[R
] N) (hf) (n : N) (r : R) : foldr Q f hf n (algebraMap R _ r) = r • n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
-/
theorem changeForm_algebraMap (r : R) : changeForm h (algebraMap R _ r) = algebraMap R _ r :=
  (foldr_algebraMap _ _ _ _ _).trans <| Eq.symm <| Algebra.algebraMap_eq_smul_one r

@[simp]
/-
**CliffordAlgebra.changeForm_one** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：changeForm_one : changeForm h (1 : CliffordAlgebra Q) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `CliffordAlgebra.changeForm_algebraMap`：changeForm_algebraMap (r : R) : c
hangeForm h (algebraMap R _ r) = algebraMap R _ r
-/
theorem changeForm_one : changeForm h (1 : CliffordAlgebra Q) = 1 := by
  simpa using changeForm_algebraMap h (1 : R)

@[simp]
/-
**CliffordAlgebra.changeForm_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem changeForm_ι (m : M) : changeForm h (ι (M := M) Q m) = ι (M := M) Q' m :=
  (foldr_ι _ _ _ _ _).trans <|
    Eq.symm <| by rw [changeFormAux_apply_apply, mul_one, contractLeft_one, sub_zero]
/-
**CliffordAlgebra.changeForm_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem changeForm_ι_mul (m : M) (x : CliffordAlgebra Q) :
    changeForm h (ι Q m * x) = ι Q' m * changeForm h x - B m⌋changeForm h x :=
  (foldr_mul _ _ _ _ _ _).trans <| by rw [foldr_ι]; rfl
/-
**CliffordAlgebra.changeForm_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem changeForm_ι_mul_ι (m₁ m₂ : M) :
    changeForm h (ι Q m₁ * ι Q m₂) = ι Q' m₁ * ι Q' m₂ - algebraMap _ _ (B m₁ m₂) := by
  rw [changeForm_ι_mul, changeForm_ι, contractLeft_ι]

/-- Theorem 23 of [grinberg_clifford_2016] -/
/-
**CliffordAlgebra.changeForm_contractLeft** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlg
ebra`。
形式化陈述：changeForm_contractLeft (d : Module.Dual R M) (x : CliffordAlgebra Q) : ch
angeForm h (d⌋x) = d⌋(changeForm h x)
参数：d : Module.Dual R M；x : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.left_induction`：left_induction {P : CliffordAlgebra Q ->
 Prop} (algebraMap : forall r : R, P (algebraMap _ _ r)) (add : forall x y, P x 
-> P y -> P (x + y))…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.contractLeft_algebraMap`：contractLeft_algebraMap (r : R)
 : d⌋algebraMap R (CliffordAlgebra Q) r = 0
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
· 使用定理 `CliffordAlgebra.changeForm_algebraMap`：changeForm_algebraMap (r : R) : c
hangeForm h (algebraMap R _ r) = algebraMap R _ r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `CliffordAlgebra.contractLeft_ι_mul`：contractLeft_ι_mul (a : M) (b : Clif
fordAlgebra Q) : d⌋(ι Q a * b) = d a • b - ι Q a * (d⌋b)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `CliffordAlgebra.changeForm_ι_mul`：changeForm_ι_mul (m : M) (x : Clifford
Algebra Q) : changeForm h (ι Q m * x) = ι Q' m * changeForm h x - B m⌋changeForm
 h x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CliffordAlgebra.contractLeft_comm`：contractLeft_comm (x : CliffordAlgebr
a Q) : d⌋(d'⌋x) = -(d'⌋(d⌋x))
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b

--- 原说明 ---
Theorem 23 of [grinberg_clifford_2016]
-/
theorem changeForm_contractLeft (d : Module.Dual R M) (x : CliffordAlgebra Q) :
    changeForm h (d⌋x) = d⌋(changeForm h x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp only [contractLeft_algebraMap, changeForm_algebraMap, map_zero]
  | add _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | ι_mul _ _ hx =>
    simp only [contractLeft_ι_mul, changeForm_ι_mul, map_sub, map_smul]
    rw [← hx, contractLeft_comm, ← sub_add, sub_neg_eq_add, ← hx]
/-
**CliffordAlgebra.changeForm_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
ra`。
形式化陈述：changeForm_self_apply (x : CliffordAlgebra Q) : changeForm (Q'
参数：x : CliffordAlgebra Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.left_induction`：left_induction {P : CliffordAlgebra Q ->
 Prop} (algebraMap : forall r : R, P (algebraMap _ _ r)) (add : forall x y, P x 
-> P y -> P (x + y))…
· 使用定理 `CliffordAlgebra.changeForm.zero_proof`：∀ {R : Type u1} [inst : CommRing 
R] {M : Type u2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Q
uadraticForm R M}, LinearMa…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.changeForm_algebraMap`：changeForm_algebraMap (r : R) : c
hangeForm h (algebraMap R _ r) = algebraMap R _ r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `CliffordAlgebra.changeForm_ι_mul`：changeForm_ι_mul (m : M) (x : Clifford
Algebra Q) : changeForm h (ι Q m * x) = ι Q' m * changeForm h x - B m⌋changeForm
 h x
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
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
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem changeForm_self_apply (x : CliffordAlgebra Q) : changeForm (Q' := Q)
    changeForm.zero_proof x = x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [changeForm_algebraMap]
  | add _ _ hx hy => rw [map_add, hx, hy]
  | ι_mul _ _ hx => rw [changeForm_ι_mul, hx, LinearMap.zero_apply, map_zero, LinearMap.zero_apply,
      sub_zero]

@[simp]
/-
**CliffordAlgebra.changeForm_self** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：changeForm_self : changeForm changeForm.zero_proof = (LinearMap.id : Cliff
ordAlgebra Q ->ₗ[R] _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CliffordAlgebra.changeForm.zero_proof`：∀ {R : Type u1} [inst : CommRing 
R] {M : Type u2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Q
uadraticForm R M}, LinearMa…
· 使用定理 `CliffordAlgebra.changeForm_self_apply`：changeForm_self_apply (x : Cliffo
rdAlgebra Q) : changeForm (Q'
-/
theorem changeForm_self :
    changeForm changeForm.zero_proof = (LinearMap.id : CliffordAlgebra Q →ₗ[R] _) :=
  LinearMap.ext <| changeForm_self_apply

/-- This is [bourbaki2007] §9 Lemma 3. -/
/-
**CliffordAlgebra.changeForm_changeForm** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
ra`。
形式化陈述：changeForm_changeForm (x : CliffordAlgebra Q) : changeForm h' (changeForm 
h x) = changeForm (changeForm.add_proof h h') x
参数：x : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.left_induction`：left_induction {P : CliffordAlgebra Q ->
 Prop} (algebraMap : forall r : R, P (algebraMap _ _ r)) (add : forall x y, P x 
-> P y -> P (x + y))…
· 使用定理 `CliffordAlgebra.changeForm.add_proof`：∀ {R : Type u1} [inst : CommRing R
] {M : Type u2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q Q' Q
'' : QuadraticForm R M} {B…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.changeForm_algebraMap`：changeForm_algebraMap (r : R) : c
hangeForm h (algebraMap R _ r) = algebraMap R _ r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `CliffordAlgebra.changeForm_ι_mul`：changeForm_ι_mul (m : M) (x : Clifford
Algebra Q) : changeForm h (ι Q m * x) = ι Q' m * changeForm h x - B m⌋changeForm
 h x
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `LinearMap.add_apply`：add_apply (f g : M ->ₛₗ[σ₁₂] M₂) (x : M) : (f + g) 
x = f x + g x
· 使用定理 `CliffordAlgebra.changeForm_contractLeft`：changeForm_contractLeft (d : Mo
dule.Dual R M) (x : CliffordAlgebra Q) : changeForm h (d⌋x) = d⌋(changeForm h x)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
This is [bourbaki2007] §9 Lemma 3.
-/
theorem changeForm_changeForm (x : CliffordAlgebra Q) :
    changeForm h' (changeForm h x) = changeForm (changeForm.add_proof h h') x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap => simp_rw [changeForm_algebraMap]
  | add _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | ι_mul _ _ hx => rw [changeForm_ι_mul, map_sub, changeForm_ι_mul, changeForm_ι_mul, hx, sub_sub,
      LinearMap.add_apply, map_add, LinearMap.add_apply, changeForm_contractLeft, hx,
      add_comm (_ : CliffordAlgebra Q'')]
/-
**CliffordAlgebra.changeForm_comp_changeForm** 是 Mathlib 中的一个定理，位于命名空间 `Clifford
Algebra`。
形式化陈述：changeForm_comp_changeForm : (changeForm h').comp (changeForm h) = changeF
orm (changeForm.add_proof h h')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CliffordAlgebra.changeForm.add_proof`：∀ {R : Type u1} [inst : CommRing R
] {M : Type u2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q Q' Q
'' : QuadraticForm R M} {B…
· 使用定理 `CliffordAlgebra.changeForm_changeForm`：changeForm_changeForm (x : Cliffo
rdAlgebra Q) : changeForm h' (changeForm h x) = changeForm (changeForm.add_proof
 h h') x
-/
theorem changeForm_comp_changeForm :
    (changeForm h').comp (changeForm h) = changeForm (changeForm.add_proof h h') :=
  LinearMap.ext <| changeForm_changeForm _ h'

/-- Any two algebras whose quadratic forms differ by a bilinear form are isomorphic as modules.

This is $\bar \lambda_B$ from [bourbaki2007] §9 Proposition 3. -/
@[simps apply]
/-
**CliffordAlgebra.changeFormEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：changeFormEquiv : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.changeForm.neg_proof`：∀ {R : Type u1} [inst : CommRing R
] {M : Type u2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q Q' :
 QuadraticForm R M} {B : L…

--- 原说明 ---
Any two algebras whose quadratic forms differ by a bilinear form are isomorphic 
as modules.

This is $\bar \lambda_B$ from [bourbaki2007] §9 Proposition 3.
-/
def changeFormEquiv : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q' :=
  { changeForm h with
    toFun := changeForm h
    invFun := changeForm (changeForm.neg_proof h)
    left_inv := fun x => by
      exact (changeForm_changeForm _ _ x).trans <|
        by simp_rw [(add_neg_cancel B), changeForm_self_apply]
    right_inv := fun x => by
      exact (changeForm_changeForm _ _ x).trans <|
        by simp_rw [(neg_add_cancel B), changeForm_self_apply] }

@[simp]
/-
**CliffordAlgebra.changeFormEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebr
a`。
形式化陈述：changeFormEquiv_symm : (changeFormEquiv h).symm = changeFormEquiv (changeF
orm.neg_proof h)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `CliffordAlgebra.changeForm.neg_proof`：∀ {R : Type u1} [inst : CommRing R
] {M : Type u2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q Q' :
 QuadraticForm R M} {B : L…
-/
theorem changeFormEquiv_symm :
    (changeFormEquiv h).symm = changeFormEquiv (changeForm.neg_proof h) :=
  LinearEquiv.ext fun _ => rfl

variable (Q)

/-- The module isomorphism to the exterior algebra.

Note that this holds more generally when `Q` is divisible by two, rather than only when `1` is
divisible by two; but that would be more awkward to use. -/
@[simp]
/-
**CliffordAlgebra.equivExterior** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：equivExterior [Invertible (2 : R)] : CliffordAlgebra Q ≃ₗ[R] ExteriorAlgeb
ra R M
参数：2 : R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.changeForm.associated_neg_proof`：∀ {R : Type u1} [inst :
 CommRing R] {M : Type u2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M
]   {Q : QuadraticForm R M} [inst_3 :…

--- 原说明 ---
The module isomorphism to the exterior algebra.

Note that this holds more generally when `Q` is divisible by two, rather than on
ly when `1` is
divisible by two; but that would be more awkward to use.
-/
def equivExterior [Invertible (2 : R)] : CliffordAlgebra Q ≃ₗ[R] ExteriorAlgebra R M :=
  changeFormEquiv changeForm.associated_neg_proof

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/
attribute [nolint simpNF] equivExterior.eq_1

/-- A `CliffordAlgebra` over a nontrivial ring is nontrivial, in characteristic not two. -/
/-
**CliffordAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `CliffordAlgebra` over a nontrivial ring is nontrivial, in characteristic not 
two.
-/
instance [Nontrivial R] [Invertible (2 : R)] :
    Nontrivial (CliffordAlgebra Q) := (equivExterior Q).symm.injective.nontrivial

end CliffordAlgebra

