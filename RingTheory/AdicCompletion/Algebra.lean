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
/--
theorem `transitionMap_ideal_mk` / 定理 `transitionMap_ideal_mk`

English:
theorem transitionMap_ideal_mk
  given: {m n : Nat} (hmn : m <= n) (x : R)
  proof: rfl

@[local simp]

中文:
定理 transitionMap_ideal_mk
  条件: {m n : 自然数} (hmn : m <= n) (x : R)
  证明: rfl

@[local simp]
-/
theorem transitionMap_ideal_mk {m n : Nat} (hmn : m <= n) (x : R) :
    transitionMap I R hmn (Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) x) =
      Ideal.Quotient.mk (I ^ m • ⊤ : Ideal R) x :=
  rfl

@[local simp]
/--
theorem `transitionMap_map_one` / 定理 `transitionMap_map_one`

English:
theorem transitionMap_map_one
  given: {m n : Nat} (hmn : m <= n)
  statement: transitionMap I R hmn 1 = 1
  proof: rfl

@[local simp]

中文:
定理 transitionMap_map_one
  条件: {m n : 自然数} (hmn : m <= n)
  结论: transitionMap I R hmn 1 = 1
  证明: rfl

@[local simp]
-/
theorem transitionMap_map_one {m n : Nat} (hmn : m <= n) : transitionMap I R hmn 1 = 1 :=
  rfl

@[local simp]
/--
theorem `transitionMap_map_mul` / 定理 `transitionMap_map_mul`

English:
theorem transitionMap_map_mul
  given: {m n : Nat} (hmn : m <= n) (x y : R ⧸ (I ^ n • ⊤ : Ideal R))
  proof: Quotient.inductionOn₂' x y (fun _ _ => rfl)

@[local simp]

中文:
定理 transitionMap_map_mul
  条件: {m n : 自然数} (hmn : m <= n) (x y : R ⧸ (I ^ n • ⊤ : 理想 R))
  证明: Quotient.inductionOn₂' x y (fun _ _ => rfl)

@[local simp]

Depends on / 依赖: Quotient, Quotient.inductionOn
-/
theorem transitionMap_map_mul {m n : Nat} (hmn : m <= n) (x y : R ⧸ (I ^ n • ⊤ : Ideal R)) :
    transitionMap I R hmn (x * y) = transitionMap I R hmn x * transitionMap I R hmn y :=
  Quotient.inductionOn₂' x y (fun _ _ => rfl)

@[local simp]
/--
theorem `transitionMap_map_pow` / 定理 `transitionMap_map_pow`

English:
theorem transitionMap_map_pow
  given: {m n a : Nat} (hmn : m <= n) (x : R ⧸ (I ^ n • ⊤ : Ideal R))
  proof: Quotient.inductionOn' x (fun _ => rfl)

中文:
定理 transitionMap_map_pow
  条件: {m n a : 自然数} (hmn : m <= n) (x : R ⧸ (I ^ n • ⊤ : 理想 R))
  证明: Quotient.inductionOn' x (fun _ => rfl)

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem transitionMap_map_pow {m n a : Nat} (hmn : m <= n) (x : R ⧸ (I ^ n • ⊤ : Ideal R)) :
    transitionMap I R hmn (x ^ a) = transitionMap I R hmn x ^ a :=
  Quotient.inductionOn' x (fun _ => rfl)

/--
Definition of `transitionMapₐ` / `transitionMapₐ` 的定义

English:
definition transitionMapₐ
  signature: {m n : Nat} (hmn : m <= n)
  body: AlgHom.ofLinearMap (transitionMap I R hmn) rfl (transitionMap_map_mul I hmn)

中文:
定义 transitionMapₐ
  签名: {m n : 自然数} (hmn : m <= n)
  定义体: AlgHom.ofLinearMap (transitionMap I R hmn) rfl (transitionMap_map_mul I hmn)

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, ofLinearMap, transitionMap, transitionMap_map_mul
-/
def transitionMapₐ {m n : Nat} (hmn : m <= n) :
    R ⧸ (I ^ n • ⊤ : Ideal R) ->ₐ[R] R ⧸ (I ^ m • ⊤ : Ideal R) :=
  AlgHom.ofLinearMap (transitionMap I R hmn) rfl (transitionMap_map_mul I hmn)

/--
Definition of `subalgebra` / `subalgebra` 的定义

English:
definition subalgebra
  signature: : Subalgebra R (forall n, R ⧸ (I ^ n • ⊤ : Ideal R))
  body: Submodule.toSubalgebra (submodule I R) (fun _ => by simp [transitionMap_map_one I])
    (fun x y hx hy m n hmn => by simp [hx hmn, hy hmn, transitionMap_map_mul I hmn])

中文:
定义 subalgebra
  签名: : 子代数 R (对任意 n, R ⧸ (I ^ n • ⊤ : 理想 R))
  定义体: Submodule.toSubalgebra (submodule I R) (fun _ => by simp [transitionMap_map_one I])
    (fun x y hx hy m n hmn => by simp [hx hmn, hy hmn, transitionMap_map_mul I hmn])

Depends on / 依赖: Submodule, Submodule.toSubalgebra, submodule, toSubalgebra, transitionMap_map_mul, transitionMap_map_one
-/
def subalgebra : Subalgebra R (forall n, R ⧸ (I ^ n • ⊤ : Ideal R)) :=
  Submodule.toSubalgebra (submodule I R) (fun _ => by simp [transitionMap_map_one I])
    (fun x y hx hy m n hmn => by simp [hx hmn, hy hmn, transitionMap_map_mul I hmn])

/--
Definition of `subring` / `subring` 的定义

English:
definition subring
  signature: : Subring (forall n, R ⧸ (I ^ n • ⊤ : Ideal R))
  body: Subalgebra.toSubring (subalgebra I)

中文:
定义 subring
  签名: : 子环 (对任意 n, R ⧸ (I ^ n • ⊤ : 理想 R))
  定义体: Subalgebra.toSubring (subalgebra I)

Depends on / 依赖: Subalgebra, Subalgebra.toSubring, subalgebra, toSubring
-/
def subring : Subring (forall n, R ⧸ (I ^ n • ⊤ : Ideal R)) :=
  Subalgebra.toSubring (subalgebra I)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (AdicCompletion I R)
  body: ⟨x.val * y.val, fun hmn => by
    simp [x.property, y.property, transitionMap_map_mul I hmn]⟩

中文:
实例 :
  签名: 乘法 (AdicCompletion I R)
  定义体: ⟨x.val * y.val, fun hmn => by
    simp [x.property, y.property, transitionMap_map_mul I hmn]⟩

Depends on / 依赖: property, transitionMap_map_mul, x.property, x.val, y.property, y.val
-/
instance : Mul (AdicCompletion I R) where
  mul x y := ⟨x.val * y.val, fun hmn => by
    simp [x.property, y.property, transitionMap_map_mul I hmn]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (AdicCompletion I R)
  body: ⟨1, by simp [transitionMap_map_one I]⟩

中文:
实例 :
  签名: 幺 (AdicCompletion I R)
  定义体: ⟨1, by simp [transitionMap_map_one I]⟩

Depends on / 依赖: transitionMap_map_one
-/
instance : One (AdicCompletion I R) where
  one := ⟨1, by simp [transitionMap_map_one I]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (AdicCompletion I R)
  body: ⟨n, fun _ => rfl⟩

中文:
实例 :
  签名: 自然数嵌入 (AdicCompletion I R)
  定义体: ⟨n, fun _ => rfl⟩
-/
instance : NatCast (AdicCompletion I R) where
  natCast n := ⟨n, fun _ => rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IntCast (AdicCompletion I R)
  body: ⟨n, fun _ => rfl⟩

中文:
实例 :
  签名: 整数嵌入 (AdicCompletion I R)
  定义体: ⟨n, fun _ => rfl⟩
-/
instance : IntCast (AdicCompletion I R) where
  intCast n := ⟨n, fun _ => rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (AdicCompletion I R) Nat
  body: ⟨x.val ^ n, fun hmn => by simp [x.property, transitionMap_map_pow I hmn]⟩

中文:
实例 :
  签名: 幂 (AdicCompletion I R) 自然数
  定义体: ⟨x.val ^ n, fun hmn => by simp [x.property, transitionMap_map_pow I hmn]⟩

Depends on / 依赖: property, transitionMap_map_pow, x.property, x.val
-/
instance : Pow (AdicCompletion I R) Nat where
  pow x n := ⟨x.val ^ n, fun hmn => by simp [x.property, transitionMap_map_pow I hmn]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (AdicCompletion I R)
  body: let f : AdicCompletion I R -> forall n, R ⧸ (I ^ n • ⊤ : Ideal R) := Subtype.val
  Subtype.val_injective.commRing f rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

中文:
实例 :
  签名: 交换环 (AdicCompletion I R)
  定义体: let f : AdicCompletion I R -> forall n, R ⧸ (I ^ n • ⊤ : Ideal R) := Subtype.val
  Subtype.val_injective.commRing f rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

Depends on / 依赖: AdicCompletion, Subtype, Subtype.val, Subtype.val_injective.commRing, commRing, val_injective
-/
instance : CommRing (AdicCompletion I R) :=
  let f : AdicCompletion I R -> forall n, R ⧸ (I ^ n • ⊤ : Ideal R) := Subtype.val
  Subtype.val_injective.commRing f rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra
  signature: S R] : Algebra S (AdicCompletion I R) where
  body: { toFun r := ⟨algebraMap S (forall n, R ⧸ (I ^ n • ⊤ : Ideal R)) r, fun hmn => by
      simp only [Pi.algebraMap_apply,
        IsScalarTower.algebraMap_apply S R (R ⧸ (I ^ _ • ⊤ : Ideal R)),
        Ideal.Quotient.algebraMap_eq, mapQ_eq_factor]
      rfl⟩
map_one' := Subtype.ext map_one _
map_mul' x y := Subtype.ext map_mul _ x y
map_zero' := Subtype.ext map_zero _
map_add' x y := Subtype.ext map_add _ x y }
commutes' r x := Subtype.ext Algebra.commutes' r x.val
smul_def' r x := Subtype.ext Algebra.smul_def' r x.val

中文:
实例 [代数
  签名: S R] : 代数 S (AdicCompletion I R) where
  定义体: { toFun r := ⟨algebraMap S (forall n, R ⧸ (I ^ n • ⊤ : Ideal R)) r, fun hmn => by
      simp only [Pi.algebraMap_apply,
        IsScalarTower.algebraMap_apply S R (R ⧸ (I ^ _ • ⊤ : Ideal R)),
        Ideal.Quotient.algebraMap_eq, mapQ_eq_factor]
      rfl⟩
map_one' := Subtype.ext map_one _
map_mul' x y := Subtype.ext map_mul _ x y
map_zero' := Subtype.ext map_zero _
map_add' x y := Subtype.ext map_add _ x y }
commutes' r x := Subtype.ext Algebra.commutes' r x.val
smul_def' r x := Subtype.ext Algebra.smul_def' r x.val

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, IsScalarTower, IsScalarTower.algebraMap_apply, Pi.algebraMap_apply, Quotient, Subtype, Subtype.ext, algebraMap, algebraMap_apply, algebraMap_eq, commutes, mapQ_eq_factor, map_add, map_mul, map_one, map_zero, smul_def
-/
instance [Algebra S R] : Algebra S (AdicCompletion I R) where
  algebraMap :=
  { toFun r := ⟨algebraMap S (forall n, R ⧸ (I ^ n • ⊤ : Ideal R)) r, fun hmn => by
      simp only [Pi.algebraMap_apply,
        IsScalarTower.algebraMap_apply S R (R ⧸ (I ^ _ • ⊤ : Ideal R)),
        Ideal.Quotient.algebraMap_eq, mapQ_eq_factor]
      rfl⟩
map_one' := Subtype.ext map_one _
map_mul' x y := Subtype.ext map_mul _ x y
map_zero' := Subtype.ext map_zero _
map_add' x y := Subtype.ext map_add _ x y }
commutes' r x := Subtype.ext Algebra.commutes' r x.val
smul_def' r x := Subtype.ext Algebra.smul_def' r x.val

/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: [Algebra S R] (s : S)
  proof: rfl

@[simp]

中文:
定理 algebraMap_apply
  条件: [代数 S R] (s : S)
  证明: rfl

@[simp]
-/
theorem algebraMap_apply [Algebra S R] (s : S) :
    algebraMap S (AdicCompletion I R) s = of I R (algebraMap S R s) := rfl

@[simp]
/--
theorem `val_one` / 定理 `val_one`

English:
theorem val_one
  given: (n : Nat)
  statement: (1 : AdicCompletion I R).val n = 1
  proof: rfl

@[simp]

中文:
定理 val_one
  条件: (n : 自然数)
  结论: (1 : AdicCompletion I R).val n = 1
  证明: rfl

@[simp]
-/
theorem val_one (n : Nat) : (1 : AdicCompletion I R).val n = 1 :=
  rfl

@[simp]
/--
theorem `val_mul` / 定理 `val_mul`

English:
theorem val_mul
  given: (n : Nat) (x y : AdicCompletion I R)
  statement: (x * y).val n = x.val n * y.val n
  proof: rfl

中文:
定理 val_mul
  条件: (n : 自然数) (x y : AdicCompletion I R)
  结论: (x * y).val n = x.val n * y.val n
  证明: rfl
-/
theorem val_mul (n : Nat) (x y : AdicCompletion I R) : (x * y).val n = x.val n * y.val n :=
  rfl

/--
Definition of `evalₐ` / `evalₐ` 的定义

English:
definition evalₐ
  signature: (n : Nat)
  body: have h : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  AlgHom.comp
    (Ideal.quotientEquivAlgOfEq R h)
    (AlgHom.ofLinearMap (eval I R n) rfl (fun _ _ => rfl))

中文:
定义 evalₐ
  签名: (n : 自然数)
  定义体: have h : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  AlgHom.comp
    (Ideal.quotientEquivAlgOfEq R h)
    (AlgHom.ofLinearMap (eval I R n) rfl (fun _ _ => rfl))

Depends on / 依赖: AlgHom, AlgHom.comp, AlgHom.ofLinearMap, Ideal.quotientEquivAlgOfEq, ofLinearMap, quotientEquivAlgOfEq
-/
def evalₐ (n : Nat) : AdicCompletion I R ->ₐ[R] R ⧸ I ^ n :=
  have h : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  AlgHom.comp
    (Ideal.quotientEquivAlgOfEq R h)
    (AlgHom.ofLinearMap (eval I R n) rfl (fun _ _ => rfl))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `factor_evalₐ_eq_eval` / 定理 `factor_evalₐ_eq_eval`

English:
theorem factor_evalₐ_eq_eval
  given: {n : Nat} (x : AdicCompletion I R) (h : I ^ n <= I ^ n • ⊤)
  proof: by
  simp [evalₐ]

中文:
定理 factor_evalₐ_eq_eval
  条件: {n : 自然数} (x : AdicCompletion I R) (h : I ^ n <= I ^ n • ⊤)
  证明: by
  simp [evalₐ]
-/
theorem factor_evalₐ_eq_eval {n : Nat} (x : AdicCompletion I R) (h : I ^ n <= I ^ n • ⊤) :
    Ideal.Quotient.factor h (evalₐ I n x) = eval I R n x := by
  simp [evalₐ]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `factor_eval_eq_evalₐ` / 定理 `factor_eval_eq_evalₐ`

English:
theorem factor_eval_eq_evalₐ
  given: {n : Nat} (x : AdicCompletion I R) (h : I ^ n • ⊤ <= I ^ n)
  proof: by
  simp [evalₐ]

中文:
定理 factor_eval_eq_evalₐ
  条件: {n : 自然数} (x : AdicCompletion I R) (h : I ^ n • ⊤ <= I ^ n)
  证明: by
  simp [evalₐ]
-/
theorem factor_eval_eq_evalₐ {n : Nat} (x : AdicCompletion I R) (h : I ^ n • ⊤ <= I ^ n) :
    factor h (eval I R n x) = evalₐ I n x := by
  simp [evalₐ]

set_option backward.isDefEq.respectTransparency false in
/--
The composition map `R →+* AdicCompletion I R →+* R ⧸ I ^ n` equals to the natural quotient map.
-/
@[simp]
/--
theorem `evalₐ_of` / 定理 `evalₐ_of`

English:
theorem evalₐ_of
  given: (n : Nat) (x : R)
  proof: by
  simp [evalₐ]

中文:
定理 evalₐ_of
  条件: (n : 自然数) (x : R)
  证明: by
  simp [evalₐ]
-/
theorem evalₐ_of (n : Nat) (x : R) :
    evalₐ I n (of I R x) = Ideal.Quotient.mk _ x := by
  simp [evalₐ]

/--
theorem `surjective_evalₐ` / 定理 `surjective_evalₐ`

English:
theorem surjective_evalₐ
  given: (n : Nat)
  statement: Function.Surjective (evalₐ I n)
  proof: by
  simp only [evalₐ, smul_eq_mul, Ideal.quotientEquivAlgOfEq_coe_eq_factorₐ,
    AlgHom.coe_comp]
  apply Function.Surjective.comp
  · exact factor_surjective Ideal.mul_le_left
  · exact eval_surjective I R n

中文:
定理 surjective_evalₐ
  条件: (n : 自然数)
  结论: 函数.满射 (evalₐ I n)
  证明: by
  simp only [evalₐ, smul_eq_mul, Ideal.quotientEquivAlgOfEq_coe_eq_factorₐ,
    AlgHom.coe_comp]
  apply Function.Surjective.comp
  · exact factor_surjective Ideal.mul_le_left
  · exact eval_surjective I R n

Depends on / 依赖: AlgHom, AlgHom.coe_comp, Function, Function.Surjective.comp, Ideal.mul_le_left, Ideal.quotientEquivAlgOfEq_coe_eq_factor, Surjective, coe_comp, eval_surjective, factor_surjective, mul_le_left, smul_eq_mul
-/
theorem surjective_evalₐ (n : Nat) : Function.Surjective (evalₐ I n) := by
  simp only [evalₐ, smul_eq_mul, Ideal.quotientEquivAlgOfEq_coe_eq_factorₐ,
    AlgHom.coe_comp]
  apply Function.Surjective.comp
  · exact factor_surjective Ideal.mul_le_left
  · exact eval_surjective I R n

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `evalₐ_mk` / 定理 `evalₐ_mk`

English:
theorem evalₐ_mk
  given: (n : Nat) (x : AdicCauchySequence I R)
  proof: by
  simp [evalₐ]

中文:
定理 evalₐ_mk
  条件: (n : 自然数) (x : AdicCauchySequence I R)
  证明: by
  simp [evalₐ]
-/
theorem evalₐ_mk (n : Nat) (x : AdicCauchySequence I R) :
    evalₐ I n (mk I R x) = Ideal.Quotient.mk (I ^ n) (x.val n) := by
  simp [evalₐ]

variable {I} in
/--
lemma `ext_evalₐ` / 引理 `ext_evalₐ`

English:
lemma ext_evalₐ
  given: {x y : AdicCompletion I R} (H : forall n, evalₐ I n x = evalₐ I n y)
  statement: x = y
  proof: by
  ext n
  have h : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  exact (Ideal.quotientEquivAlgOfEq R h).injective (H n)

中文:
引理 ext_evalₐ
  条件: {x y : AdicCompletion I R} (H : 对任意 n, evalₐ I n x = evalₐ I n y)
  结论: x = y
  证明: by
  ext n
  have h : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  exact (Ideal.quotientEquivAlgOfEq R h).injective (H n)

Depends on / 依赖: Ideal.quotientEquivAlgOfEq, injective, quotientEquivAlgOfEq
-/
lemma ext_evalₐ {x y : AdicCompletion I R} (H : forall n, evalₐ I n x = evalₐ I n y) : x = y := by
  ext n
  have h : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  exact (Ideal.quotientEquivAlgOfEq R h).injective (H n)

/--
Definition of `evalOneₐ` / `evalOneₐ` 的定义

English:
definition evalOneₐ
  signature: : AdicCompletion I R ->ₐ[R] R ⧸ I
  body: (Ideal.Quotient.factorₐ _ (by simp)).comp (evalₐ _ 1)

@[simp]

中文:
定义 evalOneₐ
  签名: : AdicCompletion I R ->ₐ[R] R ⧸ I
  定义体: (Ideal.Quotient.factorₐ _ (by simp)).comp (evalₐ _ 1)

@[simp]

Depends on / 依赖: Ideal.Quotient.factor, Quotient, l.toList, toList
-/
def evalOneₐ : AdicCompletion I R ->ₐ[R] R ⧸ I :=
  (Ideal.Quotient.factorₐ _ (by simp)).comp (evalₐ _ 1)

@[simp]
/--
lemma `evalOneₐ_of` / 引理 `evalOneₐ_of`

English:
lemma evalOneₐ_of
  given: (x : R)
  statement: evalOneₐ I (of I R x) = x
  proof: rfl

@[simp]

中文:
引理 evalOneₐ_of
  条件: (x : R)
  结论: evalOneₐ I (of I R x) = x
  证明: rfl

@[simp]
-/
lemma evalOneₐ_of (x : R) : evalOneₐ I (of I R x) = x := rfl

@[simp]
/--
lemma `factorₐ_evalₐ_one` / 引理 `factorₐ_evalₐ_one`

English:
lemma factorₐ_evalₐ_one
  given: (x : AdicCompletion I R)
  proof: rfl

中文:
引理 factorₐ_evalₐ_one
  条件: (x : AdicCompletion I R)
  证明: rfl
-/
lemma factorₐ_evalₐ_one (x : AdicCompletion I R) :
    Ideal.Quotient.factor (show I ^ 1 <= I by simp) (evalₐ I 1 x) = evalOneₐ I x :=
  rfl

/--
lemma `evalOneₐ_comp_algebraMap_eq_mk` / 引理 `evalOneₐ_comp_algebraMap_eq_mk`

English:
lemma evalOneₐ_comp_algebraMap_eq_mk
  proof: rfl

中文:
引理 evalOneₐ_comp_algebraMap_eq_mk
  证明: rfl
-/
lemma evalOneₐ_comp_algebraMap_eq_mk :
    (AdicCompletion.evalOneₐ I).toRingHom.comp (algebraMap R (AdicCompletion I R)) =
      (Ideal.Quotient.mk I) :=
  rfl

/--
lemma `evalOneₐ_surjective` / 引理 `evalOneₐ_surjective`

English:
lemma evalOneₐ_surjective
  statement: Function.Surjective (evalOneₐ I)
  proof: by
  dsimp [evalOneₐ]
  exact (Ideal.Quotient.factor_surjective (show I ^ 1 <= I by simp)).comp
    (AdicCompletion.surjective_evalₐ I 1)

中文:
引理 evalOneₐ_surjective
  结论: 函数.满射 (evalOneₐ I)
  证明: by
  dsimp [evalOneₐ]
  exact (Ideal.Quotient.factor_surjective (show I ^ 1 <= I by simp)).comp
    (AdicCompletion.surjective_evalₐ I 1)

Depends on / 依赖: AdicCompletion, AdicCompletion.surjective_eval, Ideal.Quotient.factor_surjective, Quotient, factor_surjective
-/
lemma evalOneₐ_surjective : Function.Surjective (evalOneₐ I) := by
  dsimp [evalOneₐ]
  exact (Ideal.Quotient.factor_surjective (show I ^ 1 <= I by simp)).comp
    (AdicCompletion.surjective_evalₐ I 1)

/--
Definition of `AdicCauchySequence.subalgebra` / `AdicCauchySequence.subalgebra` 的定义

English:
definition AdicCauchySequence.subalgebra
  signature: : Subalgebra R (Nat -> R)
  body: Submodule.toSubalgebra (AdicCauchySequence.submodule I R)
    (fun {m n} _ => by simp)
    (fun x y hx hy {m n} hmn => by
      simp only [Pi.mul_apply]
      exact SModEq.mul (hx hmn) (hy hmn))

中文:
定义 AdicCauchySequence.subalgebra
  签名: : 子代数 R (自然数 -> R)
  定义体: Submodule.toSubalgebra (AdicCauchySequence.submodule I R)
    (fun {m n} _ => by simp)
    (fun x y hx hy {m n} hmn => by
      simp only [Pi.mul_apply]
      exact SModEq.mul (hx hmn) (hy hmn))

Depends on / 依赖: AdicCauchySequence, AdicCauchySequence.submodule, List.Subset.refl, Pi.mul_apply, SModEq, SModEq.mul, Submodule, Submodule.toSubalgebra, Subset, mul_apply, ofList_subset, of_toList, submodule, toSubalgebra
-/
def AdicCauchySequence.subalgebra : Subalgebra R (Nat -> R) :=
  Submodule.toSubalgebra (AdicCauchySequence.submodule I R)
    (fun {m n} _ => by simp)
    (fun x y hx hy {m n} hmn => by
      simp only [Pi.mul_apply]
      exact SModEq.mul (hx hmn) (hy hmn))

/--
Definition of `AdicCauchySequence.subring` / `AdicCauchySequence.subring` 的定义

English:
definition AdicCauchySequence.subring
  signature: : Subring (Nat -> R)
  body: Subalgebra.toSubring (AdicCauchySequence.subalgebra I)

中文:
定义 AdicCauchySequence.subring
  签名: : 子环 (自然数 -> R)
  定义体: Subalgebra.toSubring (AdicCauchySequence.subalgebra I)

Depends on / 依赖: AdicCauchySequence, AdicCauchySequence.subalgebra, Subalgebra, Subalgebra.toSubring, subalgebra, toSubring
-/
def AdicCauchySequence.subring : Subring (Nat -> R) :=
  Subalgebra.toSubring (AdicCauchySequence.subalgebra I)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (AdicCauchySequence I R)
  body: ⟨x.val * y.val, fun hmn => SModEq.mul (x.property hmn) (y.property hmn)⟩

中文:
实例 :
  签名: 乘法 (AdicCauchySequence I R)
  定义体: ⟨x.val * y.val, fun hmn => SModEq.mul (x.property hmn) (y.property hmn)⟩

Depends on / 依赖: SModEq, SModEq.mul, property, x.property, x.val, y.property, y.val
-/
instance : Mul (AdicCauchySequence I R) where
  mul x y := ⟨x.val * y.val, fun hmn => SModEq.mul (x.property hmn) (y.property hmn)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (AdicCauchySequence I R)
  body: ⟨1, fun _ => rfl⟩

中文:
实例 :
  签名: 幺 (AdicCauchySequence I R)
  定义体: ⟨1, fun _ => rfl⟩
-/
instance : One (AdicCauchySequence I R) where
  one := ⟨1, fun _ => rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (AdicCauchySequence I R)
  body: ⟨n, fun _ => rfl⟩

中文:
实例 :
  签名: 自然数嵌入 (AdicCauchySequence I R)
  定义体: ⟨n, fun _ => rfl⟩
-/
instance : NatCast (AdicCauchySequence I R) where
  natCast n := ⟨n, fun _ => rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IntCast (AdicCauchySequence I R)
  body: ⟨n, fun _ => rfl⟩

中文:
实例 :
  签名: 整数嵌入 (AdicCauchySequence I R)
  定义体: ⟨n, fun _ => rfl⟩
-/
instance : IntCast (AdicCauchySequence I R) where
  intCast n := ⟨n, fun _ => rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (AdicCauchySequence I R) Nat
  body: ⟨x.val ^ n, fun hmn => SModEq.pow n (x.property hmn)⟩

中文:
实例 :
  签名: 幂 (AdicCauchySequence I R) 自然数
  定义体: ⟨x.val ^ n, fun hmn => SModEq.pow n (x.property hmn)⟩

Depends on / 依赖: SModEq, SModEq.pow, property, x.property, x.val
-/
instance : Pow (AdicCauchySequence I R) Nat where
  pow x n := ⟨x.val ^ n, fun hmn => SModEq.pow n (x.property hmn)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (AdicCauchySequence I R)
  body: let f : AdicCauchySequence I R -> (Nat -> R) := Subtype.val
  Subtype.val_injective.commRing f rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

中文:
实例 :
  签名: 交换环 (AdicCauchySequence I R)
  定义体: let f : AdicCauchySequence I R -> (Nat -> R) := Subtype.val
  Subtype.val_injective.commRing f rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

Depends on / 依赖: AdicCauchySequence, Subtype, Subtype.val, Subtype.val_injective.commRing, commRing, val_injective
-/
instance : CommRing (AdicCauchySequence I R) :=
  let f : AdicCauchySequence I R -> (Nat -> R) := Subtype.val
  Subtype.val_injective.commRing f rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R (AdicCauchySequence I R)
  body: { toFun r := ⟨algebraMap R (forall _, R) r, fun _ => rfl⟩
map_one' := Subtype.ext map_one _
map_mul' x y := Subtype.ext map_mul _ x y
map_zero' := Subtype.ext map_zero _
map_add' x y := Subtype.ext map_add _ x y }
commutes' r x := Subtype.ext Algebra.commutes' r x.val
smul_def' r x := Subtype.ext Algebra.smul_def' r x.val

@[simp]

中文:
实例 :
  签名: 代数 R (AdicCauchySequence I R)
  定义体: { toFun r := ⟨algebraMap R (forall _, R) r, fun _ => rfl⟩
map_one' := Subtype.ext map_one _
map_mul' x y := Subtype.ext map_mul _ x y
map_zero' := Subtype.ext map_zero _
map_add' x y := Subtype.ext map_add _ x y }
commutes' r x := Subtype.ext Algebra.commutes' r x.val
smul_def' r x := Subtype.ext Algebra.smul_def' r x.val

@[simp]

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.smul_def, Subtype, Subtype.ext, algebraMap, commutes, map_add, map_mul, map_one, map_zero, smul_def, x.val
-/
instance : Algebra R (AdicCauchySequence I R) where
  algebraMap :=
  { toFun r := ⟨algebraMap R (forall _, R) r, fun _ => rfl⟩
map_one' := Subtype.ext map_one _
map_mul' x y := Subtype.ext map_mul _ x y
map_zero' := Subtype.ext map_zero _
map_add' x y := Subtype.ext map_add _ x y }
commutes' r x := Subtype.ext Algebra.commutes' r x.val
smul_def' r x := Subtype.ext Algebra.smul_def' r x.val

@[simp]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (n : Nat)
  statement: (1 : AdicCauchySequence I R) n = 1
  proof: rfl

@[simp]

中文:
定理 one_apply
  条件: (n : 自然数)
  结论: (1 : AdicCauchySequence I R) n = 1
  证明: rfl

@[simp]
-/
theorem one_apply (n : Nat) : (1 : AdicCauchySequence I R) n = 1 :=
  rfl

@[simp]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (n : Nat) (f g : AdicCauchySequence I R)
  statement: (f * g) n = f n * g n
  proof: rfl

中文:
定理 mul_apply
  条件: (n : 自然数) (f g : AdicCauchySequence I R)
  结论: (f * g) n = f n * g n
  证明: rfl
-/
theorem mul_apply (n : Nat) (f g : AdicCauchySequence I R) : (f * g) n = f n * g n :=
  rfl

/-- The canonical algebra map from adic Cauchy sequences to the adic completion. -/
@[simps!]
/--
Definition of `mkₐ` / `mkₐ` 的定义

English:
definition mkₐ
  signature: : AdicCauchySequence I R ->ₐ[R] AdicCompletion I R
  body: AlgHom.ofLinearMap (mk I R) rfl (fun _ _ => rfl)

中文:
定义 mkₐ
  签名: : AdicCauchySequence I R ->ₐ[R] AdicCompletion I R
  定义体: AlgHom.ofLinearMap (mk I R) rfl (fun _ _ => rfl)

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, ofLinearMap
-/
def mkₐ : AdicCauchySequence I R ->ₐ[R] AdicCompletion I R :=
  AlgHom.ofLinearMap (mk I R) rfl (fun _ _ => rfl)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `evalₐ_mkₐ` / 定理 `evalₐ_mkₐ`

English:
theorem evalₐ_mkₐ
  given: (n : Nat) (x : AdicCauchySequence I R)
  proof: by
  simp [mkₐ]

中文:
定理 evalₐ_mkₐ
  条件: (n : 自然数) (x : AdicCauchySequence I R)
  证明: by
  simp [mkₐ]
-/
theorem evalₐ_mkₐ (n : Nat) (x : AdicCauchySequence I R) :
    evalₐ I n (mkₐ I x) = Ideal.Quotient.mk (I ^ n) (x.val n) := by
  simp [mkₐ]

/--
theorem `Ideal.mk_eq_mk` / 定理 `Ideal.mk_eq_mk`

English:
theorem Ideal.mk_eq_mk
  given: {m n : Nat} (hmn : m <= n) (r : AdicCauchySequence I R)
  proof: by
  have h : I ^ m = I ^ m • ⊤ := by simp
  rw [← Ideal.Quotient.mk_eq_mk]; rw [← Ideal.Quotient.mk_eq_mk]; rw [h]
  exact (r.property hmn).symm

中文:
定理 理想.mk_eq_mk
  条件: {m n : 自然数} (hmn : m <= n) (r : AdicCauchySequence I R)
  证明: by
  have h : I ^ m = I ^ m • ⊤ := by simp
  rw [← Ideal.Quotient.mk_eq_mk]; rw [← Ideal.Quotient.mk_eq_mk]; rw [h]
  exact (r.property hmn).symm

Depends on / 依赖: Ideal.Quotient.mk_eq_mk, Quotient, mk_eq_mk, property, r.property
-/
theorem Ideal.mk_eq_mk {m n : Nat} (hmn : m <= n) (r : AdicCauchySequence I R) :
    Ideal.Quotient.mk (I ^ m) (r.val n) = Ideal.Quotient.mk (I ^ m) (r.val m) := by
  have h : I ^ m = I ^ m • ⊤ := by simp
  rw [← Ideal.Quotient.mk_eq_mk]; rw [← Ideal.Quotient.mk_eq_mk]; rw [h]
  exact (r.property hmn).symm

/--
theorem `smul_mk` / 定理 `smul_mk`

English:
theorem smul_mk
  statement: {m n : Nat} (hmn : m <= n) (r : AdicCauchySequence I R)
  proof: by
  rw [← Submodule.Quotient.mk_smul]; rw [← Module.Quotient.mk_smul_mk]; rw [AdicCauchySequence.mk_eq_mk hmn]; rw [Ideal.mk_eq_mk I hmn]; rw [Module.Quotient.mk_smul_mk]; rw [Submodule.Quotient.mk_smul]

中文:
定理 smul_mk
  结论: {m n : 自然数} (hmn : m <= n) (r : AdicCauchySequence I R)
  证明: by
  rw [← Submodule.Quotient.mk_smul]; rw [← Module.Quotient.mk_smul_mk]; rw [AdicCauchySequence.mk_eq_mk hmn]; rw [Ideal.mk_eq_mk I hmn]; rw [Module.Quotient.mk_smul_mk]; rw [Submodule.Quotient.mk_smul]

Depends on / 依赖: Submodule, x.val
-/
theorem smul_mk {m n : Nat} (hmn : m <= n) (r : AdicCauchySequence I R)
    (x : AdicCauchySequence I M) :
    r.val n • Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (x.val n) =
      r.val m • Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (x.val m) := by
  rw [← Submodule.Quotient.mk_smul]; rw [← Module.Quotient.mk_smul_mk]; rw [AdicCauchySequence.mk_eq_mk hmn]; rw [Ideal.mk_eq_mk I hmn]; rw [Module.Quotient.mk_smul_mk]; rw [Submodule.Quotient.mk_smul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (R ⧸ (I • ⊤ : Ideal R)) (M ⧸ (I • ⊤ : Submodule R M))
  body: Quotient.liftOn r (· • x) fun b₁ b₂ h => by
      induction x using Quotient.inductionOn'
      have h : b₁ - b₂ in (I : Submodule R R) := by
        rwa [show I = I • ⊤ by simp, ← Submodule.quotientRel_def]
      rw [← sub_eq_zero]; rw [← sub_smul]; rw [Submodule.Quotient.mk''_eq_mk]; rw [← Submodule.Quotient.mk_smul]; rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul h mem_top

@[local simp]

中文:
实例 :
  签名: 标量乘法 (R ⧸ (I • ⊤ : 理想 R)) (M ⧸ (I • ⊤ : 子模 R M))
  定义体: Quotient.liftOn r (· • x) fun b₁ b₂ h => by
      induction x using Quotient.inductionOn'
      have h : b₁ - b₂ in (I : Submodule R R) := by
        rwa [show I = I • ⊤ by simp, ← Submodule.quotientRel_def]
      rw [← sub_eq_zero]; rw [← sub_smul]; rw [Submodule.Quotient.mk''_eq_mk]; rw [← Submodule.Quotient.mk_smul]; rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul h mem_top

@[local simp]

Depends on / 依赖: Quotient, Quotient.inductionOn, Quotient.liftOn, Submodule, Submodule.Quotient.mk, Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, Submodule.quotientRel_def, Submodule.smul_mem_smul, _eq_mk, inductionOn, liftOn, mem_top, mk_eq_zero, mk_smul, quotientRel_def, smul_mem_smul, sub_eq_zero, sub_smul
-/
instance : SMul (R ⧸ (I • ⊤ : Ideal R)) (M ⧸ (I • ⊤ : Submodule R M)) where
  smul r x :=
    Quotient.liftOn r (· • x) fun b₁ b₂ h => by
      induction x using Quotient.inductionOn'
      have h : b₁ - b₂ in (I : Submodule R R) := by
        rwa [show I = I • ⊤ by simp, ← Submodule.quotientRel_def]
      rw [← sub_eq_zero]; rw [← sub_smul]; rw [Submodule.Quotient.mk''_eq_mk]; rw [← Submodule.Quotient.mk_smul]; rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul h mem_top

@[local simp]
/--
theorem `mk_smul_mk` / 定理 `mk_smul_mk`

English:
theorem mk_smul_mk
  given: (r : R) (x : M)
  proof: rfl

中文:
定理 mk_smul_mk
  条件: (r : R) (x : M)
  证明: rfl

Depends on / 依赖: Submodule
-/
theorem mk_smul_mk (r : R) (x : M) :
    Ideal.Quotient.mk (I • ⊤) r • Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) x
      = r • Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) x :=
  rfl

/--
theorem `val_smul_eq_evalₐ_smul` / 定理 `val_smul_eq_evalₐ_smul`

English:
theorem val_smul_eq_evalₐ_smul
  statement: (n : Nat) (r : AdicCompletion I R)
  proof: by
  induction r using induction_on; rfl

中文:
定理 val_smul_eq_evalₐ_smul
  结论: (n : 自然数) (r : AdicCompletion I R)
  证明: by
  induction r using induction_on; rfl

Depends on / 依赖: Equiv.antisymm, antisymm, induction_on
-/
theorem val_smul_eq_evalₐ_smul (n : Nat) (r : AdicCompletion I R)
    (x : M ⧸ (I ^ n • ⊤ : Submodule R M)) : r.val n • x = evalₐ I n r • x := by
  induction r using induction_on; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module (R ⧸ (I • ⊤ : Ideal R)) (M ⧸ (I • ⊤ : Submodule R M))
  body: Function.Surjective.moduleLeft (Ideal.Quotient.mk (I • ⊤ : Ideal R))
    Ideal.Quotient.mk_surjective (fun _ _ => rfl)

中文:
实例 :
  签名: 模 (R ⧸ (I • ⊤ : 理想 R)) (M ⧸ (I • ⊤ : 子模 R M))
  定义体: Function.Surjective.moduleLeft (Ideal.Quotient.mk (I • ⊤ : Ideal R))
    Ideal.Quotient.mk_surjective (fun _ _ => rfl)

Depends on / 依赖: Equiv.antisymm_iff, Function, Function.Surjective.moduleLeft, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Quotient, Surjective, antisymm_iff, equiv_atom, inductionMut, l.toList, mk_surjective, moduleLeft, toList
-/
instance : Module (R ⧸ (I • ⊤ : Ideal R)) (M ⧸ (I • ⊤ : Submodule R M)) :=
  Function.Surjective.moduleLeft (Ideal.Quotient.mk (I • ⊤ : Ideal R))
    Ideal.Quotient.mk_surjective (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R (R ⧸ (I • ⊤ : Ideal R)) (M ⧸ (I • ⊤ : Submodule R M))
  body: by
    induction s, x using Quotient.inductionOn₂' with | _ s x
    simp only [Submodule.Quotient.mk''_eq_mk]
    rw [← Submodule.Quotient.mk_smul]; rw [Ideal.Quotient.mk_eq_mk]; rw [mk_smul_mk]; rw [smul_assoc]
    rfl

中文:
实例 :
  签名: 标量塔 R (R ⧸ (I • ⊤ : 理想 R)) (M ⧸ (I • ⊤ : 子模 R M))
  定义体: by
    induction s, x using Quotient.inductionOn₂' with | _ s x
    simp only [Submodule.Quotient.mk''_eq_mk]
    rw [← Submodule.Quotient.mk_smul]; rw [Ideal.Quotient.mk_eq_mk]; rw [mk_smul_mk]; rw [smul_assoc]
    rfl

Depends on / 依赖: Ideal.Quotient.mk_eq_mk, Quotient, Quotient.inductionOn, Submodule, Submodule.Quotient.mk, Submodule.Quotient.mk_smul, _eq_mk, mk_eq_mk, mk_smul, mk_smul_mk, smul_assoc
-/
instance : IsScalarTower R (R ⧸ (I • ⊤ : Ideal R)) (M ⧸ (I • ⊤ : Submodule R M)) where
  smul_assoc r s x := by
    induction s, x using Quotient.inductionOn₂' with | _ s x
    simp only [Submodule.Quotient.mk''_eq_mk]
    rw [← Submodule.Quotient.mk_smul]; rw [Ideal.Quotient.mk_eq_mk]; rw [mk_smul_mk]; rw [smul_assoc]
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: : SMul (AdicCompletion I R) (AdicCompletion I M) where
  body: {
    val := fun n => eval I R n r • eval I M n x
    property := fun {m n} hmn => by
      apply induction_on I R r (fun r => ?_)
      apply induction_on I M x (fun x => ?_)
      simp only [coe_eval, mapQ_eq_factor, mk_apply_coe, mkQ_apply, Ideal.Quotient.mk_eq_mk,
        mk_smul_mk, map_smul, mapQ_apply, LinearMap.id_coe, id_eq]
      rw [smul_mk I hmn]
  }

@[simp]

中文:
实例 smul
  签名: : 标量乘法 (AdicCompletion I R) (AdicCompletion I M) where
  定义体: {
    val := fun n => eval I R n r • eval I M n x
    property := fun {m n} hmn => by
      apply induction_on I R r (fun r => ?_)
      apply induction_on I M x (fun x => ?_)
      simp only [coe_eval, mapQ_eq_factor, mk_apply_coe, mkQ_apply, Ideal.Quotient.mk_eq_mk,
        mk_smul_mk, map_smul, mapQ_apply, LinearMap.id_coe, id_eq]
      rw [smul_mk I hmn]
  }

@[simp]
-/
instance smul : SMul (AdicCompletion I R) (AdicCompletion I M) where
  smul r x := {
    val := fun n => eval I R n r • eval I M n x
    property := fun {m n} hmn => by
      apply induction_on I R r (fun r => ?_)
      apply induction_on I M x (fun x => ?_)
      simp only [coe_eval, mapQ_eq_factor, mk_apply_coe, mkQ_apply, Ideal.Quotient.mk_eq_mk,
        mk_smul_mk, map_smul, mapQ_apply, LinearMap.id_coe, id_eq]
      rw [smul_mk I hmn]
  }

@[simp]
/--
theorem `smul_eval` / 定理 `smul_eval`

English:
theorem smul_eval
  given: (n : Nat) (r : AdicCompletion I R) (x : AdicCompletion I M)
  proof: rfl

中文:
定理 smul_eval
  条件: (n : 自然数) (r : AdicCompletion I R) (x : AdicCompletion I M)
  证明: rfl
-/
theorem smul_eval (n : Nat) (r : AdicCompletion I R) (x : AdicCompletion I M) :
    (r • x).val n = r.val n • x.val n :=
  rfl

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: : Module (AdicCompletion I R) (AdicCompletion I M) where
  body: by
    ext n
    simp only [smul_eval, val_one, one_smul]
  mul_smul r s x := by
    ext n
    simp only [smul_eval, val_mul, mul_smul]
  smul_zero r := by ext n; simp
  smul_add r x y := by ext n; simp
  add_smul r s x := by ext n; simp [add_smul]
  zero_smul x := by ext n; simp

中文:
实例 module
  签名: : 模 (AdicCompletion I R) (AdicCompletion I M) where
  定义体: by
    ext n
    simp only [smul_eval, val_one, one_smul]
  mul_smul r s x := by
    ext n
    simp only [smul_eval, val_mul, mul_smul]
  smul_zero r := by ext n; simp
  smul_add r x y := by ext n; simp
  add_smul r s x := by ext n; simp [add_smul]
  zero_smul x := by ext n; simp

Depends on / 依赖: add_smul, mul_smul, one_smul, smul_add, smul_eval, smul_zero, val_mul, val_one, zero_smul
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R (AdicCompletion I R) (AdicCompletion I M)
  body: by
    ext n
    rw [smul_eval]; rw [val_smul_apply]; rw [val_smul_apply]; rw [smul_eval]; rw [smul_assoc]

中文:
实例 :
  签名: 标量塔 R (AdicCompletion I R) (AdicCompletion I M)
  定义体: by
    ext n
    rw [smul_eval]; rw [val_smul_apply]; rw [val_smul_apply]; rw [smul_eval]; rw [smul_assoc]

Depends on / 依赖: smul_assoc, smul_eval, val_smul_apply
-/
instance : IsScalarTower R (AdicCompletion I R) (AdicCompletion I M) where
  smul_assoc r s x := by
    ext n
    rw [smul_eval]; rw [val_smul_apply]; rw [val_smul_apply]; rw [smul_eval]; rw [smul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A priori `AdicCompletion I R` has two `AdicCompletion I R`-module instances.
Both agree definitionally. -/
example : module I = @Algebra.toModule (AdicCompletion I R)
    (AdicCompletion I R) _ _ (Algebra.id _) := by
  with_reducible_and_instances rfl

section liftRingHom

open Quotient

variable {R S : Type*} [NonAssocSemiring R] [CommRing S] (I : Ideal S)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftRingHom` / `liftRingHom` 的定义

English:
definition liftRingHom
  signature: (f : (n : Nat) -> R ->+* S ⧸ I ^ n)
  body: fun x => ⟨fun n => (factor (le_of_eq (Ideal.mul_top _).symm)) (f n x),
    fun hkl => by simp [transitionMap, Submodule.factorPow, ← hf hkl]⟩
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

中文:
定义 liftRingHom
  签名: (f : (n : 自然数) -> R ->+* S ⧸ I ^ n)
  定义体: fun x => ⟨fun n => (factor (le_of_eq (Ideal.mul_top _).symm)) (f n x),
    fun hkl => by simp [transitionMap, Submodule.factorPow, ← hf hkl]⟩
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

Depends on / 依赖: Equiv.decidable, Ideal.mul_top, SizeOf, SizeOf.sizeOf, decidable, decidable_of_iff, decreasing_tactic, factor, le_of_eq, mem.decidable, mem_cons, mul_top, sizeOf, sizeof_pos, termination_by
-/
def liftRingHom (f : (n : Nat) -> R ->+* S ⧸ I ^ n)
    (hf : forall {m n : Nat} (hle : m <= n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m) :
    R ->+* AdicCompletion I S where
  toFun := fun x => ⟨fun n => (factor (le_of_eq (Ideal.mul_top _).symm)) (f n x),
    fun hkl => by simp [transitionMap, Submodule.factorPow, ← hf hkl]⟩
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

variable (f : (n : Nat) -> R ->+* S ⧸ I ^ n)
  (hf : forall {m n : Nat} (hle : m <= n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `factor_eval_liftRingHom` / 定理 `factor_eval_liftRingHom`

English:
theorem factor_eval_liftRingHom
  given: (n : Nat) (x : R) (h : I ^ n • ⊤ <= I ^ n)
  proof: by
  simp [liftRingHom, eval]

中文:
定理 factor_eval_liftRingHom
  条件: (n : 自然数) (x : R) (h : I ^ n • ⊤ <= I ^ n)
  证明: by
  simp [liftRingHom, eval]

Depends on / 依赖: liftRingHom
-/
theorem factor_eval_liftRingHom (n : Nat) (x : R) (h : I ^ n • ⊤ <= I ^ n) :
    factor h (eval I S n (liftRingHom I f hf x)) = f n x := by
  simp [liftRingHom, eval]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `evalₐ_liftRingHom` / 定理 `evalₐ_liftRingHom`

English:
theorem evalₐ_liftRingHom
  given: (n : Nat) (x : R)
  proof: by
  rw [← factor_eval_eq_evalₐ I _ (le_of_eq (Ideal.mul_top _))]
  simp [liftRingHom, eval]

@[simp]

中文:
定理 evalₐ_liftRingHom
  条件: (n : 自然数) (x : R)
  证明: by
  rw [← factor_eval_eq_evalₐ I _ (le_of_eq (Ideal.mul_top _))]
  simp [liftRingHom, eval]

@[simp]

Depends on / 依赖: Ideal.mul_top, le_of_eq, liftRingHom, mul_top
-/
theorem evalₐ_liftRingHom (n : Nat) (x : R) :
    evalₐ I n (liftRingHom I f hf x) = f n x := by
  rw [← factor_eval_eq_evalₐ I _ (le_of_eq (Ideal.mul_top _))]
  simp [liftRingHom, eval]

@[simp]
/--
theorem `evalₐ_comp_liftRingHom` / 定理 `evalₐ_comp_liftRingHom`

English:
theorem evalₐ_comp_liftRingHom
  given: (n : Nat)
  proof: by
  ext; simp

中文:
定理 evalₐ_comp_liftRingHom
  条件: (n : 自然数)
  证明: by
  ext; simp

Depends on / 依赖: mem_of_subset, subset_def
-/
theorem evalₐ_comp_liftRingHom (n : Nat) :
    (evalₐ I n : _ ->+* _).comp (liftRingHom I f hf) = f n := by
  ext; simp

section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra R S]

/--
Definition of `liftAlgHom` / `liftAlgHom` 的定义

English:
definition liftAlgHom
  signature: (f : (n : Nat) -> A ->ₐ[R] S ⧸ I ^ n)
  body: liftRingHom I (fun n => (f n).toRingHom) fun hle => by ext x; exact congr($(hf hle) x)
  commutes' r := ext_evalₐ fun n => by
    simp [evalₐ_liftRingHom _ _ <| fun hle => by ext x; exact congr($(hf hle) x)]

中文:
定义 liftAlgHom
  签名: (f : (n : 自然数) -> A ->ₐ[R] S ⧸ I ^ n)
  定义体: liftRingHom I (fun n => (f n).toRingHom) fun hle => by ext x; exact congr($(hf hle) x)
  commutes' r := ext_evalₐ fun n => by
    simp [evalₐ_liftRingHom _ _ <| fun hle => by ext x; exact congr($(hf hle) x)]

Depends on / 依赖: liftRingHom, toRingHom
-/
def liftAlgHom (f : (n : Nat) -> A ->ₐ[R] S ⧸ I ^ n)
    (hf : forall {m n : Nat} (hle : m <= n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m) :
    A ->ₐ[R] AdicCompletion I S where
__ := liftRingHom I (fun n => (f n).toRingHom) fun hle => by ext x; exact congr($(hf hle) x)
  commutes' r := ext_evalₐ fun n => by
    simp [evalₐ_liftRingHom _ _ <| fun hle => by ext x; exact congr($(hf hle) x)]

variable (f : (n : Nat) -> A ->ₐ[R] S ⧸ I ^ n)
  (hf : forall {m n : Nat} (hle : m <= n),
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m)

@[simp]
/--
lemma `evalₐ_liftAlgHom` / 引理 `evalₐ_liftAlgHom`

English:
lemma evalₐ_liftAlgHom
  given: (n : Nat) (x : A)
  proof: evalₐ_liftRingHom _ _ (fun hle => by ext x; exact congr($(hf hle) x)) _ _

@[simp]

中文:
引理 evalₐ_liftAlgHom
  条件: (n : 自然数) (x : A)
  证明: evalₐ_liftRingHom _ _ (fun hle => by ext x; exact congr($(hf hle) x)) _ _

@[simp]
-/
lemma evalₐ_liftAlgHom (n : Nat) (x : A) :
    evalₐ I n (liftAlgHom I f hf x) = f n x :=
  evalₐ_liftRingHom _ _ (fun hle => by ext x; exact congr($(hf hle) x)) _ _

@[simp]
/--
lemma `evalOneₐ_liftAlgHom` / 引理 `evalOneₐ_liftAlgHom`

English:
lemma evalOneₐ_liftAlgHom
  given: (x : A)
  proof: by
  simp [evalOneₐ]

中文:
引理 evalOneₐ_liftAlgHom
  条件: (x : A)
  证明: by
  simp [evalOneₐ]
-/
lemma evalOneₐ_liftAlgHom (x : A) :
    evalOneₐ I (liftAlgHom I f hf x) = Ideal.Quotient.factorₐ R (by simp) (f 1 x) := by
  simp [evalOneₐ]

end

variable [IsAdicComplete I S]

/--
Definition of `ofAlgEquiv` / `ofAlgEquiv` 的定义

English:
definition ofAlgEquiv
  signature: : S ≃ₐ[S] AdicCompletion I S where
  body: ofLinearEquiv I S
  map_mul' _ _ := by ext; simp
  commutes' _ := rfl

@[simp]

中文:
定义 ofAlgEquiv
  签名: : S ≃ₐ[S] AdicCompletion I S where
  定义体: ofLinearEquiv I S
  map_mul' _ _ := by ext; simp
  commutes' _ := rfl

@[simp]

Depends on / 依赖: ofLinearEquiv
-/
noncomputable def ofAlgEquiv : S ≃ₐ[S] AdicCompletion I S where
  __ := ofLinearEquiv I S
  map_mul' _ _ := by ext; simp
  commutes' _ := rfl

@[simp]
/--
theorem `ofAlgEquiv_apply` / 定理 `ofAlgEquiv_apply`

English:
theorem ofAlgEquiv_apply
  given: (x : S)
  statement: ofAlgEquiv I x = of I S x
  proof: by
  rfl

中文:
定理 ofAlgEquiv_apply
  条件: (x : S)
  结论: ofAlgEquiv I x = of I S x
  证明: by
  rfl
-/
theorem ofAlgEquiv_apply (x : S) : ofAlgEquiv I x = of I S x := by
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `of_ofAlgEquiv_symm` / 定理 `of_ofAlgEquiv_symm`

English:
theorem of_ofAlgEquiv_symm
  given: (x : AdicCompletion I S)
  proof: by
  simp [ofAlgEquiv]

中文:
定理 of_ofAlgEquiv_symm
  条件: (x : AdicCompletion I S)
  证明: by
  simp [ofAlgEquiv]

Depends on / 依赖: ofAlgEquiv
-/
theorem of_ofAlgEquiv_symm (x : AdicCompletion I S) :
    of I S ((ofAlgEquiv I).symm x) = x := by
  simp [ofAlgEquiv]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ofAlgEquiv_symm_of` / 定理 `ofAlgEquiv_symm_of`

English:
theorem ofAlgEquiv_symm_of
  given: (x : S)
  proof: by
  simp [ofAlgEquiv]

中文:
定理 ofAlgEquiv_symm_of
  条件: (x : S)
  证明: by
  simp [ofAlgEquiv]

Depends on / 依赖: ofAlgEquiv
-/
theorem ofAlgEquiv_symm_of (x : S) :
    (ofAlgEquiv I).symm (of I S x) = x := by
  simp [ofAlgEquiv]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mk_smul_top_ofAlgEquiv_symm` / 定理 `mk_smul_top_ofAlgEquiv_symm`

English:
theorem mk_smul_top_ofAlgEquiv_symm
  given: (n : Nat) (x : AdicCompletion I S)
  proof: by
  nth_rw 2 [← of_ofAlgEquiv_symm I x]
  simp [-of_ofAlgEquiv_symm, eval]

中文:
定理 mk_smul_top_ofAlgEquiv_symm
  条件: (n : 自然数) (x : AdicCompletion I S)
  证明: by
  nth_rw 2 [← of_ofAlgEquiv_symm I x]
  simp [-of_ofAlgEquiv_symm, eval]

Depends on / 依赖: nth_rw, of_ofAlgEquiv_symm
-/
theorem mk_smul_top_ofAlgEquiv_symm (n : Nat) (x : AdicCompletion I S) :
    Ideal.Quotient.mk (I ^ n • ⊤) ((ofAlgEquiv I).symm x) = eval I S n x := by
  nth_rw 2 [← of_ofAlgEquiv_symm I x]
  simp [-of_ofAlgEquiv_symm, eval]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mk_ofAlgEquiv_symm` / 定理 `mk_ofAlgEquiv_symm`

English:
theorem mk_ofAlgEquiv_symm
  given: (n : Nat) (x : AdicCompletion I S)
  proof: by
  simp only [evalₐ, AlgHom.coe_comp, Function.comp_apply, AlgHom.ofLinearMap_apply]
  rw [← mk_smul_top_ofAlgEquiv_symm I n x]
  simp

@[simp]

中文:
定理 mk_ofAlgEquiv_symm
  条件: (n : 自然数) (x : AdicCompletion I S)
  证明: by
  simp only [evalₐ, AlgHom.coe_comp, Function.comp_apply, AlgHom.ofLinearMap_apply]
  rw [← mk_smul_top_ofAlgEquiv_symm I n x]
  simp

@[simp]

Depends on / 依赖: AlgHom, AlgHom.coe_comp, AlgHom.ofLinearMap_apply, Function, Function.comp_apply, coe_comp, comp_apply, mk_smul_top_ofAlgEquiv_symm, ofLinearMap_apply
-/
theorem mk_ofAlgEquiv_symm (n : Nat) (x : AdicCompletion I S) :
    Ideal.Quotient.mk (I ^ n) ((ofAlgEquiv I).symm x) = evalₐ I n x := by
  simp only [evalₐ, AlgHom.coe_comp, Function.comp_apply, AlgHom.ofLinearMap_apply]
  rw [← mk_smul_top_ofAlgEquiv_symm I n x]
  simp

@[simp]
/--
lemma `mk_ofAlgEquiv_symm_eq_evalOneₐ` / 引理 `mk_ofAlgEquiv_symm_eq_evalOneₐ`

English:
lemma mk_ofAlgEquiv_symm_eq_evalOneₐ
  given: (x : AdicCompletion I S)
  proof: by
  simp [evalOneₐ, ← mk_ofAlgEquiv_symm]

中文:
引理 mk_ofAlgEquiv_symm_eq_evalOneₐ
  条件: (x : AdicCompletion I S)
  证明: by
  simp [evalOneₐ, ← mk_ofAlgEquiv_symm]

Depends on / 依赖: mk_ofAlgEquiv_symm
-/
lemma mk_ofAlgEquiv_symm_eq_evalOneₐ (x : AdicCompletion I S) :
    Ideal.Quotient.mk I ((ofAlgEquiv I).symm x) = evalOneₐ I x := by
  simp [evalOneₐ, ← mk_ofAlgEquiv_symm]

end liftRingHom

section

variable {A : Type*} [CommRing A] [Algebra R A] [Algebra R S]

/--
Definition of `kerProj` / `kerProj` 的定义

English:
definition kerProj
  signature: {f : S ->ₐ[R] A} (hf : Function.Surjective f)
  body: (Ideal.quotientKerAlgEquivOfSurjective hf).toAlgHom.comp
    (AdicCompletion.evalOneₐ <| RingHom.ker f).restrictScalars R

@[simp]

中文:
定义 kerProj
  签名: {f : S ->ₐ[R] A} (hf : 函数.满射 f)
  定义体: (Ideal.quotientKerAlgEquivOfSurjective hf).toAlgHom.comp
    (AdicCompletion.evalOneₐ <| RingHom.ker f).restrictScalars R

@[simp]

Depends on / 依赖: AdicCompletion, AdicCompletion.evalOne, Ideal.quotientKerAlgEquivOfSurjective, RingHom, RingHom.ker, quotientKerAlgEquivOfSurjective, restrictScalars, toAlgHom, toAlgHom.comp
-/
noncomputable def kerProj {f : S ->ₐ[R] A} (hf : Function.Surjective f) :
    AdicCompletion (RingHom.ker f) S ->ₐ[R] A :=
(Ideal.quotientKerAlgEquivOfSurjective hf).toAlgHom.comp
    (AdicCompletion.evalOneₐ <| RingHom.ker f).restrictScalars R

@[simp]
/--
lemma `kerProj_of` / 引理 `kerProj_of`

English:
lemma kerProj_of
  given: {f : S ->ₐ[R] A} (hf : Function.Surjective f) (x : S)
  proof: rfl

中文:
引理 kerProj_of
  条件: {f : S ->ₐ[R] A} (hf : 函数.满射 f) (x : S)
  证明: rfl
-/
lemma kerProj_of {f : S ->ₐ[R] A} (hf : Function.Surjective f) (x : S) :
    kerProj hf (.of _ _ x) = f x :=
  rfl

/--
lemma `kerProj_surjective` / 引理 `kerProj_surjective`

English:
lemma kerProj_surjective
  given: {f : S ->ₐ[R] A} (hf : Function.Surjective f)
  proof: by
  dsimp [kerProj]
  exact (AlgEquiv.surjective _).comp (evalOneₐ_surjective _)

中文:
引理 kerProj_surjective
  条件: {f : S ->ₐ[R] A} (hf : 函数.满射 f)
  证明: by
  dsimp [kerProj]
  exact (AlgEquiv.surjective _).comp (evalOneₐ_surjective _)

Depends on / 依赖: AlgEquiv, AlgEquiv.surjective, kerProj, surjective
-/
lemma kerProj_surjective {f : S ->ₐ[R] A} (hf : Function.Surjective f) :
    Function.Surjective (kerProj hf) := by
  dsimp [kerProj]
  exact (AlgEquiv.surjective _).comp (evalOneₐ_surjective _)

end

end AdicCompletion
