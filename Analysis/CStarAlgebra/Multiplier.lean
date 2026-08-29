/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Jon Bannon
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Multiplier Algebra of a C⋆-algebra

Define the multiplier algebra of a C⋆-algebra as the algebra (over `𝕜`) of double centralizers,
for which we provide the localized notation `𝓜(𝕜, A)`. A double centralizer is a pair of
continuous linear maps `L R : A →L[𝕜] A` satisfying the intertwining condition `R x * y = x * L y`.

There is a natural embedding `A → 𝓜(𝕜, A)` which sends `a : A` to the continuous linear maps
`L R : A →L[𝕜] A` given by left and right multiplication by `a`, and we provide this map as a
coercion.

The multiplier algebra corresponds to a non-commutative Stone–Čech compactification in the sense
that when the algebra `A` is commutative, it can be identified with `C₀(X, ℂ)` for some locally
compact Hausdorff space `X`, and in that case `𝓜(𝕜, A)` can be identified with `C(β X, ℂ)`.

## Implementation notes

We make the hypotheses on `𝕜` as weak as possible so that, in particular, this construction works
for both `𝕜 = ℝ` and `𝕜 = ℂ`.

The reader familiar with C⋆-algebra theory may recognize that one
only needs `L` and `R` to be functions instead of continuous linear maps, at least when `A` is a
C⋆-algebra. Our intention is simply to eventually provide a constructor for this situation.

We pull back the `NormedAlgebra` structure (and everything contained therein) through the
ring (even algebra) homomorphism
`DoubleCentralizer.toProdMulOppositeHom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ` which
sends `a : 𝓜(𝕜, A)` to `(a.fst, MulOpposite.op a.snd)`. The star structure is provided
separately.

## References

* https://en.wikipedia.org/wiki/Multiplier_algebra

## TODO

+ Define a type synonym for `𝓜(𝕜, A)` which is equipped with the strict uniform space structure
  and show it is complete
+ Show that the image of `A` in `𝓜(𝕜, A)` is an essential ideal
+ Prove the universal property of `𝓜(𝕜, A)`
+ Construct a double centralizer from a pair of maps (not necessarily linear or continuous)
  `L : A → A`, `R : A → A` satisfying the centrality condition `∀ x y, R x * y = x * L y`.
+ Show that if `A` is unital, then `A ≃⋆ₐ[𝕜] 𝓜(𝕜, A)`.
-/

@[expose] public section


open NNReal ENNReal ContinuousLinearMap MulOpposite

universe u v

/--
Definition of `DoubleCentralizer` / `DoubleCentralizer` 的定义

English:
structure DoubleCentralizer
  parameters: (𝕜 : Type u) (A : Type v) [NontriviallyNormedField 𝕜]
  axioms and operations (1):
    - central : forall x y : A, snd x * y = x * fst y

中文:
结构 DoubleCentralizer
  参数: (𝕜 : 类型u) (A : 类型v) [NontriviallyNormedField 𝕜]
  公理与运算 (1 个):
    - central : 对任意 x y : A, snd x * y = x * fst y
-/
structure DoubleCentralizer (𝕜 : Type u) (A : Type v) [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] extends
    (A ->L[𝕜] A) × (A ->L[𝕜] A) where
  /-- The centrality condition that the maps linear maps intertwine one another. -/
  central : forall x y : A, snd x * y = x * fst y

@[inherit_doc]
scoped[MultiplierAlgebra] notation "𝓜(" 𝕜 ", " A ")" => DoubleCentralizer 𝕜 A

open MultiplierAlgebra

@[ext]
/--
lemma `DoubleCentralizer.ext` / 引理 `DoubleCentralizer.ext`

English:
lemma DoubleCentralizer.ext
  statement: (𝕜 : Type u) (A : Type v) [NontriviallyNormedField 𝕜]
  proof: by
  cases a
  cases b
  simpa using h

中文:
引理 DoubleCentralizer.ext
  结论: (𝕜 : 类型u) (A : 类型v) [NontriviallyNormedField 𝕜]
  证明: by
  cases a
  cases b
  simpa using h
-/
lemma DoubleCentralizer.ext (𝕜 : Type u) (A : Type v) [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]
    (a b : 𝓜(𝕜, A)) (h : a.toProd = b.toProd) : a = b := by
  cases a
  cases b
  simpa using h

namespace DoubleCentralizer

section NontriviallyNormed

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
variable [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]

/-!
### Algebraic structure

Because the multiplier algebra is defined as the algebra of double centralizers, there is a natural
injection `DoubleCentralizer.toProdMulOpposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ`
defined by `fun a ↦ (a.fst, MulOpposite.op a.snd)`. We use this map to pull back the ring, module
and algebra structure from `(A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ` to `𝓜(𝕜, A)`. -/

variable {𝕜 A}

/--
theorem `range_toProd` / 定理 `range_toProd`

English:
theorem range_toProd
  proof: Set.ext fun x =>
    ⟨by
      rintro ⟨a, rfl⟩
      exact a.central, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

中文:
定理 range_toProd
  证明: Set.ext fun x =>
    ⟨by
      rintro ⟨a, rfl⟩
      exact a.central, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

Depends on / 依赖: Set.ext, a.central, central
-/
theorem range_toProd :
    Set.range toProd = { lr : (A ->L[𝕜] A) × (A ->L[𝕜] A) | forall x y, lr.2 x * y = x * lr.1 y } :=
  Set.ext fun x =>
    ⟨by
      rintro ⟨a, rfl⟩
      exact a.central, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add 𝓜(𝕜, A) where
  body: { toProd := a.toProd + b.toProd
      central := fun x y =>
        show (a.snd + b.snd) x * y = x * (a.fst + b.fst) y by
          simp only [add_apply, mul_add, add_mul, central] }

中文:
实例 instAdd
  签名: : Add 𝓜(𝕜, A) where
  定义体: { toProd := a.toProd + b.toProd
      central := fun x y =>
        show (a.snd + b.snd) x * y = x * (a.fst + b.fst) y by
          simp only [add_apply, mul_add, add_mul, central] }

Depends on / 依赖: a.fst, a.snd, a.toProd, add_apply, add_mul, b.fst, b.snd, b.toProd, central, mul_add, toProd
-/
instance instAdd : Add 𝓜(𝕜, A) where
  add a b :=
    { toProd := a.toProd + b.toProd
      central := fun x y =>
        show (a.snd + b.snd) x * y = x * (a.fst + b.fst) y by
          simp only [add_apply, mul_add, add_mul, central] }

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero 𝓜(𝕜, A) where
  body: { toProd := 0
      central := fun x y => (zero_mul y).trans (mul_zero x).symm }

中文:
实例 instZero
  签名: : Zero 𝓜(𝕜, A) where
  定义体: { toProd := 0
      central := fun x y => (zero_mul y).trans (mul_zero x).symm }

Depends on / 依赖: central, mul_zero, toProd, zero_mul
-/
instance instZero : Zero 𝓜(𝕜, A) where
  zero :=
    { toProd := 0
      central := fun x y => (zero_mul y).trans (mul_zero x).symm }

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg 𝓜(𝕜, A) where
  body: { toProd := -a.toProd
      central := fun x y =>
        show -a.snd x * y = x * -a.fst y by
          simp only [neg_mul, mul_neg, central] }

中文:
实例 instNeg
  签名: : Neg 𝓜(𝕜, A) where
  定义体: { toProd := -a.toProd
      central := fun x y =>
        show -a.snd x * y = x * -a.fst y by
          simp only [neg_mul, mul_neg, central] }

Depends on / 依赖: a.fst, a.snd, a.toProd, central, mul_neg, neg_mul, toProd
-/
instance instNeg : Neg 𝓜(𝕜, A) where
  neg a :=
    { toProd := -a.toProd
      central := fun x y =>
        show -a.snd x * y = x * -a.fst y by
          simp only [neg_mul, mul_neg, central] }

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub 𝓜(𝕜, A) where
  body: { toProd := a.toProd - b.toProd
      central := fun x y =>
        show (a.snd - b.snd) x * y = x * (a.fst - b.fst) y by
          simp only [sub_apply, _root_.sub_mul, _root_.mul_sub, central] }

中文:
实例 instSub
  签名: : Sub 𝓜(𝕜, A) where
  定义体: { toProd := a.toProd - b.toProd
      central := fun x y =>
        show (a.snd - b.snd) x * y = x * (a.fst - b.fst) y by
          simp only [sub_apply, _root_.sub_mul, _root_.mul_sub, central] }

Depends on / 依赖: _root_, _root_.mul_sub, _root_.sub_mul, a.fst, a.snd, a.toProd, b.fst, b.snd, b.toProd, central, mul_sub, sub_apply, sub_mul, toProd
-/
instance instSub : Sub 𝓜(𝕜, A) where
  sub a b :=
    { toProd := a.toProd - b.toProd
      central := fun x y =>
        show (a.snd - b.snd) x * y = x * (a.fst - b.fst) y by
          simp only [sub_apply, _root_.sub_mul, _root_.mul_sub, central] }

section Scalars

variable {S : Type*} [Monoid S] [DistribMulAction S A] [SMulCommClass 𝕜 S A]
  [ContinuousConstSMul S A] [IsScalarTower S A A] [SMulCommClass S A A]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul S 𝓜(𝕜, A) where
  body: { toProd := s • a.toProd
      central := fun x y =>
        show (s • a.snd) x * y = x * (s • a.fst) y by
          simp only [smul_apply, mul_smul_comm, smul_mul_assoc, central] }

@[simp]

中文:
实例 instSMul
  签名: : SMul S 𝓜(𝕜, A) where
  定义体: { toProd := s • a.toProd
      central := fun x y =>
        show (s • a.snd) x * y = x * (s • a.fst) y by
          simp only [smul_apply, mul_smul_comm, smul_mul_assoc, central] }

@[simp]

Depends on / 依赖: a.fst, a.snd, a.toProd, central, mul_smul_comm, smul_apply, smul_mul_assoc, toProd
-/
instance instSMul : SMul S 𝓜(𝕜, A) where
  smul s a :=
    { toProd := s • a.toProd
      central := fun x y =>
        show (s • a.snd) x * y = x * (s • a.fst) y by
          simp only [smul_apply, mul_smul_comm, smul_mul_assoc, central] }

@[simp]
/--
theorem `smul_toProd` / 定理 `smul_toProd`

English:
theorem smul_toProd
  given: (s : S) (a : 𝓜(𝕜, A))
  statement: (s • a).toProd = s • a.toProd
  proof: rfl

中文:
定理 smul_toProd
  条件: (s : S) (a : 𝓜(𝕜, A))
  结论: (s • a).toProd = s • a.toProd
  证明: rfl
-/
theorem smul_toProd (s : S) (a : 𝓜(𝕜, A)) : (s • a).toProd = s • a.toProd :=
  rfl

/--
theorem `smul_fst` / 定理 `smul_fst`

English:
theorem smul_fst
  given: (s : S) (a : 𝓜(𝕜, A))
  statement: (s • a).fst = s • a.fst
  proof: rfl

中文:
定理 smul_fst
  条件: (s : S) (a : 𝓜(𝕜, A))
  结论: (s • a).fst = s • a.fst
  证明: rfl
-/
theorem smul_fst (s : S) (a : 𝓜(𝕜, A)) : (s • a).fst = s • a.fst :=
  rfl

/--
theorem `smul_snd` / 定理 `smul_snd`

English:
theorem smul_snd
  given: (s : S) (a : 𝓜(𝕜, A))
  statement: (s • a).snd = s • a.snd
  proof: rfl

中文:
定理 smul_snd
  条件: (s : S) (a : 𝓜(𝕜, A))
  结论: (s • a).snd = s • a.snd
  证明: rfl
-/
theorem smul_snd (s : S) (a : 𝓜(𝕜, A)) : (s • a).snd = s • a.snd :=
  rfl

variable {T : Type*} [Monoid T] [DistribMulAction T A] [SMulCommClass 𝕜 T A]
  [ContinuousConstSMul T A] [IsScalarTower T A A] [SMulCommClass T A A]

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul S T] [IsScalarTower S T A]
  body: ext (𝕜 := 𝕜) (A := A) _ _ smul_assoc _ _ a.toProd

中文:
实例 instIsScalarTower
  签名: [SMul S T] [IsScalarTower S T A]
  定义体: ext (𝕜 := 𝕜) (A := A) _ _ smul_assoc _ _ a.toProd

Depends on / 依赖: a.toProd, smul_assoc, toProd
-/
instance instIsScalarTower [SMul S T] [IsScalarTower S T A] : IsScalarTower S T 𝓜(𝕜, A) where
smul_assoc _ _ a := ext (𝕜 := 𝕜) (A := A) _ _ smul_assoc _ _ a.toProd

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMulCommClass S T A]
  body: ext (𝕜 := 𝕜) (A := A) _ _ smul_comm _ _ a.toProd

中文:
实例 instSMulCommClass
  签名: [SMulCommClass S T A]
  定义体: ext (𝕜 := 𝕜) (A := A) _ _ smul_comm _ _ a.toProd

Depends on / 依赖: a.toProd, smul_comm, toProd
-/
instance instSMulCommClass [SMulCommClass S T A] : SMulCommClass S T 𝓜(𝕜, A) where
smul_comm _ _ a := ext (𝕜 := 𝕜) (A := A) _ _ smul_comm _ _ a.toProd

/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: {R : Type*} [Semiring R] [Module R A] [SMulCommClass 𝕜 R A]
  body: ext (𝕜 := 𝕜) (A := A) _ _ op_smul_eq_smul _ a.toProd

中文:
实例 instIsCentralScalar
  签名: {R : 类型} [Semiring R] [Module R A] [SMulCommClass 𝕜 R A]
  定义体: ext (𝕜 := 𝕜) (A := A) _ _ op_smul_eq_smul _ a.toProd

Depends on / 依赖: a.toProd, op_smul_eq_smul, toProd
-/
instance instIsCentralScalar {R : Type*} [Semiring R] [Module R A] [SMulCommClass 𝕜 R A]
    [ContinuousConstSMul R A] [IsScalarTower R A A] [SMulCommClass R A A] [Module Rᵐᵒᵖ A]
    [IsCentralScalar R A] : IsCentralScalar R 𝓜(𝕜, A) where
op_smul_eq_smul _ a := ext (𝕜 := 𝕜) (A := A) _ _ op_smul_eq_smul _ a.toProd

end Scalars

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One 𝓜(𝕜, A)
  body: ⟨⟨1, fun _x _y => rfl⟩⟩

中文:
实例 instOne
  签名: : One 𝓜(𝕜, A)
  定义体: ⟨⟨1, fun _x _y => rfl⟩⟩
-/
instance instOne : One 𝓜(𝕜, A) :=
  ⟨⟨1, fun _x _y => rfl⟩⟩

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul 𝓜(𝕜, A) where
  body: { toProd := (a.fst.comp b.fst, b.snd.comp a.snd)
      central := fun x y => show b.snd (a.snd x) * y = x * a.fst (b.fst y) by simp only [central] }

中文:
实例 instMul
  签名: : Mul 𝓜(𝕜, A) where
  定义体: { toProd := (a.fst.comp b.fst, b.snd.comp a.snd)
      central := fun x y => show b.snd (a.snd x) * y = x * a.fst (b.fst y) by simp only [central] }

Depends on / 依赖: a.fst, a.fst.comp, a.snd, b.fst, b.snd, b.snd.comp, central, toProd
-/
instance instMul : Mul 𝓜(𝕜, A) where
  mul a b :=
    { toProd := (a.fst.comp b.fst, b.snd.comp a.snd)
      central := fun x y => show b.snd (a.snd x) * y = x * a.fst (b.fst y) by simp only [central] }

/--
Instance `instNatCast` / 实例 `instNatCast`

English:
instance instNatCast
  signature: : NatCast 𝓜(𝕜, A) where
  body: ⟨n, fun x y => by
      rw [Prod.snd_natCast]; rw [Prod.fst_natCast]
      simp only [← Nat.smul_one_eq_cast, smul_apply, one_apply_eq_self, mul_smul_comm,
        smul_mul_assoc]⟩

中文:
实例 instNatCast
  签名: : 自然数Cast 𝓜(𝕜, A) where
  定义体: ⟨n, fun x y => by
      rw [Prod.snd_natCast]; rw [Prod.fst_natCast]
      simp only [← Nat.smul_one_eq_cast, smul_apply, one_apply_eq_self, mul_smul_comm,
        smul_mul_assoc]⟩

Depends on / 依赖: Nat.smul_one_eq_cast, Prod.fst_natCast, Prod.snd_natCast, fst_natCast, mul_smul_comm, one_apply_eq_self, smul_apply, smul_mul_assoc, smul_one_eq_cast, snd_natCast
-/
instance instNatCast : NatCast 𝓜(𝕜, A) where
  natCast n :=
    ⟨n, fun x y => by
      rw [Prod.snd_natCast]; rw [Prod.fst_natCast]
      simp only [← Nat.smul_one_eq_cast, smul_apply, one_apply_eq_self, mul_smul_comm,
        smul_mul_assoc]⟩

/--
Instance `instIntCast` / 实例 `instIntCast`

English:
instance instIntCast
  signature: : IntCast 𝓜(𝕜, A) where
  body: ⟨n, fun x y => by
      rw [Prod.snd_intCast]; rw [Prod.fst_intCast]
      simp only [← Int.smul_one_eq_cast, smul_apply, one_apply_eq_self, mul_smul_comm,
        smul_mul_assoc]⟩

中文:
实例 instIntCast
  签名: : 整数Cast 𝓜(𝕜, A) where
  定义体: ⟨n, fun x y => by
      rw [Prod.snd_intCast]; rw [Prod.fst_intCast]
      simp only [← Int.smul_one_eq_cast, smul_apply, one_apply_eq_self, mul_smul_comm,
        smul_mul_assoc]⟩

Depends on / 依赖: Int.smul_one_eq_cast, Prod.fst_intCast, Prod.snd_intCast, fst_intCast, mul_smul_comm, one_apply_eq_self, smul_apply, smul_mul_assoc, smul_one_eq_cast, snd_intCast
-/
instance instIntCast : IntCast 𝓜(𝕜, A) where
  intCast n :=
    ⟨n, fun x y => by
      rw [Prod.snd_intCast]; rw [Prod.fst_intCast]
      simp only [← Int.smul_one_eq_cast, smul_apply, one_apply_eq_self, mul_smul_comm,
        smul_mul_assoc]⟩

/--
Instance `instPow` / 实例 `instPow`

English:
instance instPow
  signature: : Pow 𝓜(𝕜, A) Nat where
  body: ⟨a.toProd ^ n, fun x y => by
      induction n generalizing x y with
      | zero => rfl
      | succ k hk =>
        rw [Prod.pow_snd]; rw [Prod.pow_fst] at hk ⊢
        rw [pow_succ' a.snd]; rw [mul_apply_eq_comp]; rw [a.central]; rw [hk]; rw [pow_succ a.fst]; rw [mul_apply_eq_comp]⟩

中文:
实例 instPow
  签名: : Pow 𝓜(𝕜, A) 自然数 where
  定义体: ⟨a.toProd ^ n, fun x y => by
      induction n generalizing x y with
      | zero => rfl
      | succ k hk =>
        rw [Prod.pow_snd]; rw [Prod.pow_fst] at hk ⊢
        rw [pow_succ' a.snd]; rw [mul_apply_eq_comp]; rw [a.central]; rw [hk]; rw [pow_succ a.fst]; rw [mul_apply_eq_comp]⟩

Depends on / 依赖: Prod.pow_fst, Prod.pow_snd, a.central, a.fst, a.snd, a.toProd, central, generalizing, mul_apply_eq_comp, pow_fst, pow_snd, pow_succ, toProd
-/
instance instPow : Pow 𝓜(𝕜, A) Nat where
  pow a n :=
    ⟨a.toProd ^ n, fun x y => by
      induction n generalizing x y with
      | zero => rfl
      | succ k hk =>
        rw [Prod.pow_snd]; rw [Prod.pow_fst] at hk ⊢
        rw [pow_succ' a.snd]; rw [mul_apply_eq_comp]; rw [a.central]; rw [hk]; rw [pow_succ a.fst]; rw [mul_apply_eq_comp]⟩

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited 𝓜(𝕜, A)
  body: ⟨0⟩

@[simp]

中文:
实例 instInhabited
  签名: : Inhabited 𝓜(𝕜, A)
  定义体: ⟨0⟩

@[simp]
-/
instance instInhabited : Inhabited 𝓜(𝕜, A) :=
  ⟨0⟩

@[simp]
/--
theorem `add_toProd` / 定理 `add_toProd`

English:
theorem add_toProd
  given: (a b : 𝓜(𝕜, A))
  statement: (a + b).toProd = a.toProd + b.toProd
  proof: rfl

@[simp]

中文:
定理 add_toProd
  条件: (a b : 𝓜(𝕜, A))
  结论: (a + b).toProd = a.toProd + b.toProd
  证明: rfl

@[simp]
-/
theorem add_toProd (a b : 𝓜(𝕜, A)) : (a + b).toProd = a.toProd + b.toProd :=
  rfl

@[simp]
/--
theorem `zero_toProd` / 定理 `zero_toProd`

English:
theorem zero_toProd
  statement: (0 : 𝓜(𝕜, A)).toProd = 0
  proof: rfl

@[simp]

中文:
定理 zero_toProd
  结论: (0 : 𝓜(𝕜, A)).toProd = 0
  证明: rfl

@[simp]
-/
theorem zero_toProd : (0 : 𝓜(𝕜, A)).toProd = 0 :=
  rfl

@[simp]
/--
theorem `neg_toProd` / 定理 `neg_toProd`

English:
theorem neg_toProd
  given: (a : 𝓜(𝕜, A))
  statement: (-a).toProd = -a.toProd
  proof: rfl

@[simp]

中文:
定理 neg_toProd
  条件: (a : 𝓜(𝕜, A))
  结论: (-a).toProd = -a.toProd
  证明: rfl

@[simp]
-/
theorem neg_toProd (a : 𝓜(𝕜, A)) : (-a).toProd = -a.toProd :=
  rfl

@[simp]
/--
theorem `sub_toProd` / 定理 `sub_toProd`

English:
theorem sub_toProd
  given: (a b : 𝓜(𝕜, A))
  statement: (a - b).toProd = a.toProd - b.toProd
  proof: rfl

@[simp]

中文:
定理 sub_toProd
  条件: (a b : 𝓜(𝕜, A))
  结论: (a - b).toProd = a.toProd - b.toProd
  证明: rfl

@[simp]
-/
theorem sub_toProd (a b : 𝓜(𝕜, A)) : (a - b).toProd = a.toProd - b.toProd :=
  rfl

@[simp]
/--
theorem `one_toProd` / 定理 `one_toProd`

English:
theorem one_toProd
  statement: (1 : 𝓜(𝕜, A)).toProd = 1
  proof: rfl

@[simp]

中文:
定理 one_toProd
  结论: (1 : 𝓜(𝕜, A)).toProd = 1
  证明: rfl

@[simp]
-/
theorem one_toProd : (1 : 𝓜(𝕜, A)).toProd = 1 :=
  rfl

@[simp]
/--
theorem `natCast_toProd` / 定理 `natCast_toProd`

English:
theorem natCast_toProd
  given: (n : Nat)
  statement: (n : 𝓜(𝕜, A)).toProd = n
  proof: rfl

@[simp]

中文:
定理 natCast_toProd
  条件: (n : 自然数)
  结论: (n : 𝓜(𝕜, A)).toProd = n
  证明: rfl

@[simp]
-/
theorem natCast_toProd (n : Nat) : (n : 𝓜(𝕜, A)).toProd = n :=
  rfl

@[simp]
/--
theorem `intCast_toProd` / 定理 `intCast_toProd`

English:
theorem intCast_toProd
  given: (n : Int)
  statement: (n : 𝓜(𝕜, A)).toProd = n
  proof: rfl

@[simp]

中文:
定理 intCast_toProd
  条件: (n : 整数)
  结论: (n : 𝓜(𝕜, A)).toProd = n
  证明: rfl

@[simp]
-/
theorem intCast_toProd (n : Int) : (n : 𝓜(𝕜, A)).toProd = n :=
  rfl

@[simp]
/--
theorem `pow_toProd` / 定理 `pow_toProd`

English:
theorem pow_toProd
  given: (n : Nat) (a : 𝓜(𝕜, A))
  statement: (a ^ n).toProd = a.toProd ^ n
  proof: rfl

中文:
定理 pow_toProd
  条件: (n : 自然数) (a : 𝓜(𝕜, A))
  结论: (a ^ n).toProd = a.toProd ^ n
  证明: rfl
-/
theorem pow_toProd (n : Nat) (a : 𝓜(𝕜, A)) : (a ^ n).toProd = a.toProd ^ n :=
  rfl

/--
theorem `add_fst` / 定理 `add_fst`

English:
theorem add_fst
  given: (a b : 𝓜(𝕜, A))
  statement: (a + b).fst = a.fst + b.fst
  proof: rfl

中文:
定理 add_fst
  条件: (a b : 𝓜(𝕜, A))
  结论: (a + b).fst = a.fst + b.fst
  证明: rfl
-/
theorem add_fst (a b : 𝓜(𝕜, A)) : (a + b).fst = a.fst + b.fst :=
  rfl

/--
theorem `add_snd` / 定理 `add_snd`

English:
theorem add_snd
  given: (a b : 𝓜(𝕜, A))
  statement: (a + b).snd = a.snd + b.snd
  proof: rfl

中文:
定理 add_snd
  条件: (a b : 𝓜(𝕜, A))
  结论: (a + b).snd = a.snd + b.snd
  证明: rfl
-/
theorem add_snd (a b : 𝓜(𝕜, A)) : (a + b).snd = a.snd + b.snd :=
  rfl

/--
theorem `zero_fst` / 定理 `zero_fst`

English:
theorem zero_fst
  statement: (0 : 𝓜(𝕜, A)).fst = 0
  proof: rfl

中文:
定理 zero_fst
  结论: (0 : 𝓜(𝕜, A)).fst = 0
  证明: rfl

Depends on / 依赖: Neg.neg, Subtype, Subtype.map
-/
theorem zero_fst : (0 : 𝓜(𝕜, A)).fst = 0 :=
  rfl

/--
theorem `zero_snd` / 定理 `zero_snd`

English:
theorem zero_snd
  statement: (0 : 𝓜(𝕜, A)).snd = 0
  proof: rfl

中文:
定理 zero_snd
  结论: (0 : 𝓜(𝕜, A)).snd = 0
  证明: rfl
-/
theorem zero_snd : (0 : 𝓜(𝕜, A)).snd = 0 :=
  rfl

/--
theorem `neg_fst` / 定理 `neg_fst`

English:
theorem neg_fst
  given: (a : 𝓜(𝕜, A))
  statement: (-a).fst = -a.fst
  proof: rfl

中文:
定理 neg_fst
  条件: (a : 𝓜(𝕜, A))
  结论: (-a).fst = -a.fst
  证明: rfl

Depends on / 依赖: Neg.neg, Subtype, Subtype.map
-/
theorem neg_fst (a : 𝓜(𝕜, A)) : (-a).fst = -a.fst :=
  rfl

/--
theorem `neg_snd` / 定理 `neg_snd`

English:
theorem neg_snd
  given: (a : 𝓜(𝕜, A))
  statement: (-a).snd = -a.snd
  proof: rfl

中文:
定理 neg_snd
  条件: (a : 𝓜(𝕜, A))
  结论: (-a).snd = -a.snd
  证明: rfl
-/
theorem neg_snd (a : 𝓜(𝕜, A)) : (-a).snd = -a.snd :=
  rfl

/--
theorem `sub_fst` / 定理 `sub_fst`

English:
theorem sub_fst
  given: (a b : 𝓜(𝕜, A))
  statement: (a - b).fst = a.fst - b.fst
  proof: rfl

中文:
定理 sub_fst
  条件: (a b : 𝓜(𝕜, A))
  结论: (a - b).fst = a.fst - b.fst
  证明: rfl
-/
theorem sub_fst (a b : 𝓜(𝕜, A)) : (a - b).fst = a.fst - b.fst :=
  rfl

/--
theorem `sub_snd` / 定理 `sub_snd`

English:
theorem sub_snd
  given: (a b : 𝓜(𝕜, A))
  statement: (a - b).snd = a.snd - b.snd
  proof: rfl

中文:
定理 sub_snd
  条件: (a b : 𝓜(𝕜, A))
  结论: (a - b).snd = a.snd - b.snd
  证明: rfl
-/
theorem sub_snd (a b : 𝓜(𝕜, A)) : (a - b).snd = a.snd - b.snd :=
  rfl

/--
theorem `one_fst` / 定理 `one_fst`

English:
theorem one_fst
  statement: (1 : 𝓜(𝕜, A)).fst = 1
  proof: rfl

中文:
定理 one_fst
  结论: (1 : 𝓜(𝕜, A)).fst = 1
  证明: rfl
-/
theorem one_fst : (1 : 𝓜(𝕜, A)).fst = 1 :=
  rfl

/--
theorem `one_snd` / 定理 `one_snd`

English:
theorem one_snd
  statement: (1 : 𝓜(𝕜, A)).snd = 1
  proof: rfl

@[simp]

中文:
定理 one_snd
  结论: (1 : 𝓜(𝕜, A)).snd = 1
  证明: rfl

@[simp]
-/
theorem one_snd : (1 : 𝓜(𝕜, A)).snd = 1 :=
  rfl

@[simp]
/--
theorem `mul_fst` / 定理 `mul_fst`

English:
theorem mul_fst
  given: (a b : 𝓜(𝕜, A))
  statement: (a * b).fst = a.fst * b.fst
  proof: rfl

@[simp]

中文:
定理 mul_fst
  条件: (a b : 𝓜(𝕜, A))
  结论: (a * b).fst = a.fst * b.fst
  证明: rfl

@[simp]
-/
theorem mul_fst (a b : 𝓜(𝕜, A)) : (a * b).fst = a.fst * b.fst :=
  rfl

@[simp]
/--
theorem `mul_snd` / 定理 `mul_snd`

English:
theorem mul_snd
  given: (a b : 𝓜(𝕜, A))
  statement: (a * b).snd = b.snd * a.snd
  proof: rfl

中文:
定理 mul_snd
  条件: (a b : 𝓜(𝕜, A))
  结论: (a * b).snd = b.snd * a.snd
  证明: rfl
-/
theorem mul_snd (a b : 𝓜(𝕜, A)) : (a * b).snd = b.snd * a.snd :=
  rfl

/--
theorem `natCast_fst` / 定理 `natCast_fst`

English:
theorem natCast_fst
  given: (n : Nat)
  statement: (n : 𝓜(𝕜, A)).fst = n
  proof: rfl

中文:
定理 natCast_fst
  条件: (n : 自然数)
  结论: (n : 𝓜(𝕜, A)).fst = n
  证明: rfl
-/
theorem natCast_fst (n : Nat) : (n : 𝓜(𝕜, A)).fst = n :=
  rfl

/--
theorem `natCast_snd` / 定理 `natCast_snd`

English:
theorem natCast_snd
  given: (n : Nat)
  statement: (n : 𝓜(𝕜, A)).snd = n
  proof: rfl

中文:
定理 natCast_snd
  条件: (n : 自然数)
  结论: (n : 𝓜(𝕜, A)).snd = n
  证明: rfl
-/
theorem natCast_snd (n : Nat) : (n : 𝓜(𝕜, A)).snd = n :=
  rfl

/--
theorem `intCast_fst` / 定理 `intCast_fst`

English:
theorem intCast_fst
  given: (n : Int)
  statement: (n : 𝓜(𝕜, A)).fst = n
  proof: rfl

中文:
定理 intCast_fst
  条件: (n : 整数)
  结论: (n : 𝓜(𝕜, A)).fst = n
  证明: rfl
-/
theorem intCast_fst (n : Int) : (n : 𝓜(𝕜, A)).fst = n :=
  rfl

/--
theorem `intCast_snd` / 定理 `intCast_snd`

English:
theorem intCast_snd
  given: (n : Int)
  statement: (n : 𝓜(𝕜, A)).snd = n
  proof: rfl

中文:
定理 intCast_snd
  条件: (n : 整数)
  结论: (n : 𝓜(𝕜, A)).snd = n
  证明: rfl
-/
theorem intCast_snd (n : Int) : (n : 𝓜(𝕜, A)).snd = n :=
  rfl

/--
theorem `pow_fst` / 定理 `pow_fst`

English:
theorem pow_fst
  given: (n : Nat) (a : 𝓜(𝕜, A))
  statement: (a ^ n).fst = a.fst ^ n
  proof: rfl

中文:
定理 pow_fst
  条件: (n : 自然数) (a : 𝓜(𝕜, A))
  结论: (a ^ n).fst = a.fst ^ n
  证明: rfl
-/
theorem pow_fst (n : Nat) (a : 𝓜(𝕜, A)) : (a ^ n).fst = a.fst ^ n :=
  rfl

/--
theorem `pow_snd` / 定理 `pow_snd`

English:
theorem pow_snd
  given: (n : Nat) (a : 𝓜(𝕜, A))
  statement: (a ^ n).snd = a.snd ^ n
  proof: rfl

中文:
定理 pow_snd
  条件: (n : 自然数) (a : 𝓜(𝕜, A))
  结论: (a ^ n).snd = a.snd ^ n
  证明: rfl
-/
theorem pow_snd (n : Nat) (a : 𝓜(𝕜, A)) : (a ^ n).snd = a.snd ^ n :=
  rfl

/--
Definition of `toProdMulOpposite` / `toProdMulOpposite` 的定义

English:
definition toProdMulOpposite
  signature: : 𝓜(𝕜, A) -> (A ->L[𝕜] A) × (A ->L[𝕜] A)ᵐᵒᵖ
  body: fun a =>
  (a.fst, MulOpposite.op a.snd)

中文:
定义 toProdMulOpposite
  签名: : 𝓜(𝕜, A) -> (A ->L[𝕜] A) × (A ->L[𝕜] A)ᵐᵒᵖ
  定义体: fun a =>
  (a.fst, MulOpposite.op a.snd)
-/
def toProdMulOpposite : 𝓜(𝕜, A) -> (A ->L[𝕜] A) × (A ->L[𝕜] A)ᵐᵒᵖ := fun a =>
  (a.fst, MulOpposite.op a.snd)

/--
theorem `toProdMulOpposite_injective` / 定理 `toProdMulOpposite_injective`

English:
theorem toProdMulOpposite_injective
  proof: fun _a _b h =>
    let h' := Prod.ext_iff.mp h
ext (𝕜 := 𝕜) (A := A) _ _ Prod.ext h'.1 MulOpposite.op_injective h'.2

中文:
定理 toProdMulOpposite_injective
  证明: fun _a _b h =>
    let h' := Prod.ext_iff.mp h
ext (𝕜 := 𝕜) (A := A) _ _ Prod.ext h'.1 MulOpposite.op_injective h'.2

Depends on / 依赖: MulOpposite, MulOpposite.op_injective, Prod.ext, Prod.ext_iff.mp, ext_iff, op_injective
-/
theorem toProdMulOpposite_injective :
    Function.Injective (toProdMulOpposite : 𝓜(𝕜, A) -> (A ->L[𝕜] A) × (A ->L[𝕜] A)ᵐᵒᵖ) :=
  fun _a _b h =>
    let h' := Prod.ext_iff.mp h
ext (𝕜 := 𝕜) (A := A) _ _ Prod.ext h'.1 MulOpposite.op_injective h'.2

/--
theorem `range_toProdMulOpposite` / 定理 `range_toProdMulOpposite`

English:
theorem range_toProdMulOpposite
  proof: Set.ext fun x =>
    ⟨by
      rintro ⟨a, rfl⟩
      exact a.central, fun hx => ⟨⟨(x.1, unop x.2), hx⟩, Prod.ext rfl rfl⟩⟩

中文:
定理 range_toProdMulOpposite
  证明: Set.ext fun x =>
    ⟨by
      rintro ⟨a, rfl⟩
      exact a.central, fun hx => ⟨⟨(x.1, unop x.2), hx⟩, Prod.ext rfl rfl⟩⟩

Depends on / 依赖: Prod.ext, Set.ext, a.central, central
-/
theorem range_toProdMulOpposite :
    Set.range toProdMulOpposite =
      { lr : (A ->L[𝕜] A) × (A ->L[𝕜] A)ᵐᵒᵖ | forall x y, unop lr.2 x * y = x * lr.1 y } :=
  Set.ext fun x =>
    ⟨by
      rintro ⟨a, rfl⟩
      exact a.central, fun hx => ⟨⟨(x.1, unop x.2), hx⟩, Prod.ext rfl rfl⟩⟩

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: : Ring 𝓜(𝕜, A)
  body: toProdMulOpposite_injective.ring _ rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _x _n => Prod.ext rfl <| MulOpposite.op_smul _ _)
    (fun _x _n => Prod.ext rfl <| MulOpposite.op_smul _ _)
    (fun _x _n => Prod.ext rfl <| MulOpposite.op_pow _ _) (fun _ => rfl) 

中文:
实例 instRing
  签名: : Ring 𝓜(𝕜, A)
  定义体: toProdMulOpposite_injective.ring _ rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _x _n => Prod.ext rfl <| MulOpposite.op_smul _ _)
    (fun _x _n => Prod.ext rfl <| MulOpposite.op_smul _ _)
    (fun _x _n => Prod.ext rfl <| MulOpposite.op_pow _ _) (fun _ => rfl) 

Depends on / 依赖: MulOpposite, MulOpposite.op_pow, MulOpposite.op_smul, Prod.ext, op_pow, op_smul, toProdMulOpposite_injective, toProdMulOpposite_injective.ring
-/
instance instRing : Ring 𝓜(𝕜, A) :=
  toProdMulOpposite_injective.ring _ rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _x _n => Prod.ext rfl <| MulOpposite.op_smul _ _)
    (fun _x _n => Prod.ext rfl <| MulOpposite.op_smul _ _)
    (fun _x _n => Prod.ext rfl <| MulOpposite.op_pow _ _) (fun _ => rfl) fun _ => rfl

/-- The canonical map `DoubleCentralizer.toProd` as an additive group homomorphism. -/
@[simps]
/--
Definition of `toProdHom` / `toProdHom` 的定义

English:
definition toProdHom
  signature: : 𝓜(𝕜, A) ->+ (A ->L[𝕜] A) × (A ->L[𝕜] A) where
  body: toProd
  map_zero' := rfl
  map_add' _x _y := rfl

中文:
定义 toProdHom
  签名: : 𝓜(𝕜, A) ->+ (A ->L[𝕜] A) × (A ->L[𝕜] A) where
  定义体: toProd
  map_zero' := rfl
  map_add' _x _y := rfl

Depends on / 依赖: toProd
-/
noncomputable def toProdHom : 𝓜(𝕜, A) ->+ (A ->L[𝕜] A) × (A ->L[𝕜] A) where
  toFun := toProd
  map_zero' := rfl
  map_add' _x _y := rfl

/-- The canonical map `DoubleCentralizer.toProdMulOpposite` as a ring homomorphism. -/
@[simps]
/--
Definition of `toProdMulOppositeHom` / `toProdMulOppositeHom` 的定义

English:
definition toProdMulOppositeHom
  signature: : 𝓜(𝕜, A) ->+* (A ->L[𝕜] A) × (A ->L[𝕜] A)ᵐᵒᵖ where
  body: toProdMulOpposite
  map_zero' := rfl
  map_one' := rfl
  map_add' _x _y := rfl
  map_mul' _x _y := rfl

中文:
定义 toProdMulOppositeHom
  签名: : 𝓜(𝕜, A) ->+* (A ->L[𝕜] A) × (A ->L[𝕜] A)ᵐᵒᵖ where
  定义体: toProdMulOpposite
  map_zero' := rfl
  map_one' := rfl
  map_add' _x _y := rfl
  map_mul' _x _y := rfl

Depends on / 依赖: toProdMulOpposite
-/
def toProdMulOppositeHom : 𝓜(𝕜, A) ->+* (A ->L[𝕜] A) × (A ->L[𝕜] A)ᵐᵒᵖ where
  toFun := toProdMulOpposite
  map_zero' := rfl
  map_one' := rfl
  map_add' _x _y := rfl
  map_mul' _x _y := rfl

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: {S : Type*} [Semiring S] [Module S A] [SMulCommClass 𝕜 S A]
  body: Function.Injective.module S toProdHom (ext (𝕜 := 𝕜) (A := A)) fun _x _y => rfl

中文:
实例 instModule
  签名: {S : 类型} [Semiring S] [Module S A] [SMulCommClass 𝕜 S A]
  定义体: Function.Injective.module S toProdHom (ext (𝕜 := 𝕜) (A := A)) fun _x _y => rfl

Depends on / 依赖: Function, Function.Injective.module, Injective, module, toProdHom
-/
noncomputable instance instModule {S : Type*} [Semiring S] [Module S A] [SMulCommClass 𝕜 S A]
    [ContinuousConstSMul S A] [IsScalarTower S A A] [SMulCommClass S A A] : Module S 𝓜(𝕜, A) :=
  Function.Injective.module S toProdHom (ext (𝕜 := 𝕜) (A := A)) fun _x _y => rfl

-- TODO: generalize to `Algebra S 𝓜(𝕜, A)` once `ContinuousLinearMap.algebra` is generalized.
/--
Instance `instAlgebra` / 实例 `instAlgebra`

English:
instance instAlgebra
  signature: : Algebra 𝕜 𝓜(𝕜, A) where
  body: { toFun k :=
      { toProd := algebraMap 𝕜 ((A ->L[𝕜] A) × (A ->L[𝕜] A)) k
        central := fun x y => by
          simp_rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
            one_apply_eq_self, mul_smul_comm, smul_mul_assoc] }
map_one' := ext (𝕜 := 𝕜) (A := A) _ _ map

中文:
实例 instAlgebra
  签名: : Algebra 𝕜 𝓜(𝕜, A) where
  定义体: { toFun k :=
      { toProd := algebraMap 𝕜 ((A ->L[𝕜] A) × (A ->L[𝕜] A)) k
        central := fun x y => by
          simp_rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
            one_apply_eq_self, mul_smul_comm, smul_mul_assoc] }
map_one' := ext (𝕜 := 𝕜) (A := A) _ _ map

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Algebra.commutes, Prod.algebraMap_apply, Prod.ext, algebraMap, algebraMap_apply, algebraMap_eq_smul_one, central, commutes, map_mul, map_one, map_zero, mul_smul_comm, one_apply_eq_self, simp_rw, smul_apply, smul_mul_assoc, toProd
-/
instance instAlgebra : Algebra 𝕜 𝓜(𝕜, A) where
  algebraMap :=
  { toFun k :=
      { toProd := algebraMap 𝕜 ((A ->L[𝕜] A) × (A ->L[𝕜] A)) k
        central := fun x y => by
          simp_rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
            one_apply_eq_self, mul_smul_comm, smul_mul_assoc] }
map_one' := ext (𝕜 := 𝕜) (A := A) _ _ map_one algebraMap 𝕜 ((A ->L[𝕜] A) × (A ->L[𝕜] A))
    map_mul' _ _ :=
ext (𝕜 := 𝕜) (A := A) _ _
        Prod.ext (map_mul (algebraMap 𝕜 (A ->L[𝕜] A)) _ _)
          ((map_mul (algebraMap 𝕜 (A ->L[𝕜] A)) _ _).trans (Algebra.commutes _ _))
map_zero' := ext (𝕜 := 𝕜) (A := A) _ _ map_zero algebraMap 𝕜 ((A ->L[𝕜] A) × (A ->L[𝕜] A))
map_add' _ _ := ext (𝕜 := 𝕜) (A := A) _ _
      map_add (algebraMap 𝕜 ((A ->L[𝕜] A) × (A ->L[𝕜] A))) _ _ }
commutes' _ _ := ext (𝕜 := 𝕜) (A := A) _ _
    Prod.ext (Algebra.commutes _ _) (Algebra.commutes _ _).symm
smul_def' _ _ := ext (𝕜 := 𝕜) (A := A) _ _
    Prod.ext (Algebra.smul_def _ _) ((Algebra.smul_def _ _).trans <| Algebra.commutes _ _)

@[simp]
/--
theorem `algebraMap_toProd` / 定理 `algebraMap_toProd`

English:
theorem algebraMap_toProd
  given: (k : 𝕜)
  statement: (algebraMap 𝕜 𝓜(𝕜, A) k).toProd = algebraMap 𝕜 _ k
  proof: rfl

中文:
定理 algebraMap_toProd
  条件: (k : 𝕜)
  结论: (algebraMap 𝕜 𝓜(𝕜, A) k).toProd = algebraMap 𝕜 _ k
  证明: rfl
-/
theorem algebraMap_toProd (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).toProd = algebraMap 𝕜 _ k :=
  rfl

/--
theorem `algebraMap_fst` / 定理 `algebraMap_fst`

English:
theorem algebraMap_fst
  given: (k : 𝕜)
  statement: (algebraMap 𝕜 𝓜(𝕜, A) k).fst = algebraMap 𝕜 _ k
  proof: rfl

中文:
定理 algebraMap_fst
  条件: (k : 𝕜)
  结论: (algebraMap 𝕜 𝓜(𝕜, A) k).fst = algebraMap 𝕜 _ k
  证明: rfl
-/
theorem algebraMap_fst (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).fst = algebraMap 𝕜 _ k :=
  rfl

/--
theorem `algebraMap_snd` / 定理 `algebraMap_snd`

English:
theorem algebraMap_snd
  given: (k : 𝕜)
  statement: (algebraMap 𝕜 𝓜(𝕜, A) k).snd = algebraMap 𝕜 _ k
  proof: rfl

中文:
定理 algebraMap_snd
  条件: (k : 𝕜)
  结论: (algebraMap 𝕜 𝓜(𝕜, A) k).snd = algebraMap 𝕜 _ k
  证明: rfl
-/
theorem algebraMap_snd (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).snd = algebraMap 𝕜 _ k :=
  rfl

/-!
### Star structure
-/


section Star

variable [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A]

/--
Instance `instStar` / 实例 `instStar`

English:
instance instStar
  signature: : Star 𝓜(𝕜, A) where
  body: { fst :=
        (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A ->L⋆[𝕜] A).comp a.snd).comp
          ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A ->L⋆[𝕜] A)
      snd :=
        (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A ->L⋆[𝕜] A).comp a.fst).comp
          ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A ->L⋆[𝕜] A)
      central := fun x y => by
        sim

中文:
实例 instStar
  签名: : Star 𝓜(𝕜, A) where
  定义体: { fst :=
        (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A ->L⋆[𝕜] A).comp a.snd).comp
          ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A ->L⋆[𝕜] A)
      snd :=
        (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A ->L⋆[𝕜] A).comp a.fst).comp
          ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A ->L⋆[𝕜] A)
      central := fun x y => by
        sim

Depends on / 依赖: a.central, a.fst, a.snd, central, congr_arg, star_mul, star_star
-/
instance instStar : Star 𝓜(𝕜, A) where
  star a :=
    { fst :=
        (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A ->L⋆[𝕜] A).comp a.snd).comp
          ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A ->L⋆[𝕜] A)
      snd :=
        (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A ->L⋆[𝕜] A).comp a.fst).comp
          ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A ->L⋆[𝕜] A)
      central := fun x y => by
        simpa only [star_mul, star_star]
          using! (congr_arg star (a.central (star y) (star x))).symm }

@[simp]
/--
theorem `star_fst` / 定理 `star_fst`

English:
theorem star_fst
  given: (a : 𝓜(𝕜, A)) (b : A)
  statement: (star a).fst b = star (a.snd (star b))
  proof: rfl

@[simp]

中文:
定理 star_fst
  条件: (a : 𝓜(𝕜, A)) (b : A)
  结论: (star a).fst b = star (a.snd (star b))
  证明: rfl

@[simp]
-/
theorem star_fst (a : 𝓜(𝕜, A)) (b : A) : (star a).fst b = star (a.snd (star b)) :=
  rfl

@[simp]
/--
theorem `star_snd` / 定理 `star_snd`

English:
theorem star_snd
  given: (a : 𝓜(𝕜, A)) (b : A)
  statement: (star a).snd b = star (a.fst (star b))
  proof: rfl

中文:
定理 star_snd
  条件: (a : 𝓜(𝕜, A)) (b : A)
  结论: (star a).snd b = star (a.fst (star b))
  证明: rfl
-/
theorem star_snd (a : 𝓜(𝕜, A)) (b : A) : (star a).snd b = star (a.fst (star b)) :=
  rfl

/--
Instance `instStarAddMonoid` / 实例 `instStarAddMonoid`

English:
instance instStarAddMonoid
  signature: : StarAddMonoid 𝓜(𝕜, A)
  body: { DoubleCentralizer.instStar with
    star_involutive _ := by ext <;> simp
    star_add _ _ := by ext <;> simp }

中文:
实例 instStarAddMonoid
  签名: : StarAddMonoid 𝓜(𝕜, A)
  定义体: { DoubleCentralizer.instStar with
    star_involutive _ := by ext <;> simp
    star_add _ _ := by ext <;> simp }

Depends on / 依赖: DoubleCentralizer, DoubleCentralizer.instStar, instStar, star_add, star_involutive
-/
instance instStarAddMonoid : StarAddMonoid 𝓜(𝕜, A) :=
  { DoubleCentralizer.instStar with
    star_involutive _ := by ext <;> simp
    star_add _ _ := by ext <;> simp }

/--
Instance `instStarRing` / 实例 `instStarRing`

English:
instance instStarRing
  signature: : StarRing 𝓜(𝕜, A)
  body: { DoubleCentralizer.instStarAddMonoid with
    star_mul _ _ := by ext <;> simp }

中文:
实例 instStarRing
  签名: : StarRing 𝓜(𝕜, A)
  定义体: { DoubleCentralizer.instStarAddMonoid with
    star_mul _ _ := by ext <;> simp }

Depends on / 依赖: DoubleCentralizer, DoubleCentralizer.instStarAddMonoid, instStarAddMonoid, star_mul
-/
instance instStarRing : StarRing 𝓜(𝕜, A) :=
  { DoubleCentralizer.instStarAddMonoid with
    star_mul _ _ := by ext <;> simp }

/--
Instance `instStarModule` / 实例 `instStarModule`

English:
instance instStarModule
  signature: : StarModule 𝕜 𝓜(𝕜, A)
  body: { DoubleCentralizer.instStarAddMonoid (𝕜 := 𝕜) (A := A) with
    star_smul _ _ := by ext <;> exact star_smul _ _ }

中文:
实例 instStarModule
  签名: : StarModule 𝕜 𝓜(𝕜, A)
  定义体: { DoubleCentralizer.instStarAddMonoid (𝕜 := 𝕜) (A := A) with
    star_smul _ _ := by ext <;> exact star_smul _ _ }

Depends on / 依赖: DoubleCentralizer, DoubleCentralizer.instStarAddMonoid, instStarAddMonoid, star_smul
-/
instance instStarModule : StarModule 𝕜 𝓜(𝕜, A) :=
  { DoubleCentralizer.instStarAddMonoid (𝕜 := 𝕜) (A := A) with
    star_smul _ _ := by ext <;> exact star_smul _ _ }

end Star

/-!
### Coercion from an algebra into its multiplier algebra
-/

variable (𝕜) in
/-- The natural coercion of `A` into `𝓜(𝕜, A)` given by sending `a : A` to the pair of linear
maps `Lₐ Rₐ : A →L[𝕜] A` given by left- and right-multiplication by `a`, respectively.

Warning: if `A = 𝕜`, then this is a coercion which is not definitionally equal to the
`algebraMap 𝕜 𝓜(𝕜, 𝕜)` coercion, but these are propositionally equal. See
`DoubleCentralizer.coe_eq_algebraMap` below. -/
@[coe]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def coe (a : A)
  body: { fst := ContinuousLinearMap.mul 𝕜 A a
    snd := (ContinuousLinearMap.mul 𝕜 A).flip a
    central := fun _x _y => mul_assoc _ _ _ }

中文:
定义 noncomputable
  签名: def coe (a : A)
  定义体: { fst := ContinuousLinearMap.mul 𝕜 A a
    snd := (ContinuousLinearMap.mul 𝕜 A).flip a
    central := fun _x _y => mul_assoc _ _ _ }
-/
protected noncomputable def coe (a : A) : 𝓜(𝕜, A) :=
  { fst := ContinuousLinearMap.mul 𝕜 A a
    snd := (ContinuousLinearMap.mul 𝕜 A).flip a
    central := fun _x _y => mul_assoc _ _ _ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC A 𝓜(𝕜, A)
  body: DoubleCentralizer.coe 𝕜

@[simp, norm_cast]

中文:
实例 :
  签名: CoeTC A 𝓜(𝕜, A)
  定义体: DoubleCentralizer.coe 𝕜

@[simp, norm_cast]

Depends on / 依赖: DoubleCentralizer, DoubleCentralizer.coe
-/
noncomputable instance : CoeTC A 𝓜(𝕜, A) where
  coe := DoubleCentralizer.coe 𝕜

@[simp, norm_cast]
/--
theorem `coe_fst` / 定理 `coe_fst`

English:
theorem coe_fst
  given: (a : A)
  statement: (a : 𝓜(𝕜, A)).fst = ContinuousLinearMap.mul 𝕜 A a
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_fst
  条件: (a : A)
  结论: (a : 𝓜(𝕜, A)).fst = ContinuousLinearMap.mul 𝕜 A a
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_fst (a : A) : (a : 𝓜(𝕜, A)).fst = ContinuousLinearMap.mul 𝕜 A a :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_snd` / 定理 `coe_snd`

English:
theorem coe_snd
  given: (a : A)
  statement: (a : 𝓜(𝕜, A)).snd = (ContinuousLinearMap.mul 𝕜 A).flip a
  proof: rfl

中文:
定理 coe_snd
  条件: (a : A)
  结论: (a : 𝓜(𝕜, A)).snd = (ContinuousLinearMap.mul 𝕜 A).flip a
  证明: rfl
-/
theorem coe_snd (a : A) : (a : 𝓜(𝕜, A)).snd = (ContinuousLinearMap.mul 𝕜 A).flip a :=
  rfl

/--
theorem `coe_eq_algebraMap` / 定理 `coe_eq_algebraMap`

English:
theorem coe_eq_algebraMap
  statement: (DoubleCentralizer.coe 𝕜 : 𝕜 -> 𝓜(𝕜, 𝕜)) = algebraMap 𝕜 𝓜(𝕜, 𝕜)
  proof: by
  ext x : 3
  · rfl -- `fst` is defeq
  · refine ContinuousLinearMap.ext fun y => ?_
    exact mul_comm y x -- `snd` multiplies on the wrong side

中文:
定理 coe_eq_algebraMap
  结论: (DoubleCentralizer.coe 𝕜 : 𝕜 -> 𝓜(𝕜, 𝕜)) = algebraMap 𝕜 𝓜(𝕜, 𝕜)
  证明: by
  ext x : 3
  · rfl -- `fst` is defeq
  · refine ContinuousLinearMap.ext fun y => ?_
    exact mul_comm y x -- `snd` multiplies on the wrong side

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext, mul_comm, multiplies
-/
theorem coe_eq_algebraMap : (DoubleCentralizer.coe 𝕜 : 𝕜 -> 𝓜(𝕜, 𝕜)) = algebraMap 𝕜 𝓜(𝕜, 𝕜) := by
  ext x : 3
  · rfl -- `fst` is defeq
  · refine ContinuousLinearMap.ext fun y => ?_
    exact mul_comm y x -- `snd` multiplies on the wrong side

/-- The coercion of an algebra into its multiplier algebra as a non-unital star algebra
homomorphism. -/
@[simps]
/--
Definition of `coeHom` / `coeHom` 的定义

English:
definition coeHom
  signature: [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A]
  body: a
map_smul' _ _ := ext _ _ _ _ Prod.ext (map_smul _ _ _) (map_smul _ _ _)
map_zero' := ext _ _ _ _ Prod.ext (map_zero _) (map_zero _)
map_add' _ _ := ext _ _ _ _ Prod.ext (map_add _ _ _) (map_add _ _ _)
map_mul' _ _ := ext _ _ _ _ Prod.ext
    (ContinuousLinearMap.ext fun _ => (mul_assoc _ _ _))
   

中文:
定义 coeHom
  签名: [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A]
  定义体: a
map_smul' _ _ := ext _ _ _ _ Prod.ext (map_smul _ _ _) (map_smul _ _ _)
map_zero' := ext _ _ _ _ Prod.ext (map_zero _) (map_zero _)
map_add' _ _ := ext _ _ _ _ Prod.ext (map_add _ _ _) (map_add _ _ _)
map_mul' _ _ := ext _ _ _ _ Prod.ext
    (ContinuousLinearMap.ext fun _ => (mul_assoc _ _ _))
   
-/
noncomputable def coeHom [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A] :
    A ->⋆ₙₐ[𝕜] 𝓜(𝕜, A) where
  toFun a := a
map_smul' _ _ := ext _ _ _ _ Prod.ext (map_smul _ _ _) (map_smul _ _ _)
map_zero' := ext _ _ _ _ Prod.ext (map_zero _) (map_zero _)
map_add' _ _ := ext _ _ _ _ Prod.ext (map_add _ _ _) (map_add _ _ _)
map_mul' _ _ := ext _ _ _ _ Prod.ext
    (ContinuousLinearMap.ext fun _ => (mul_assoc _ _ _))
    (ContinuousLinearMap.ext fun _ => (mul_assoc _ _ _).symm)
map_star' _ := ext _ _ _ _ Prod.ext
    (ContinuousLinearMap.ext fun _ => (star_star_mul _ _).symm)
    (ContinuousLinearMap.ext fun _ => (star_mul_star _ _).symm)

/-!
### Norm structures
We define the norm structure on `𝓜(𝕜, A)` as the pullback under
`DoubleCentralizer.toProdMulOppositeHom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ`, which
provides a definitional isometric embedding. Consequently, completeness of `𝓜(𝕜, A)` is obtained
by proving that the range of this map is closed.

In addition, we prove that `𝓜(𝕜, A)` is a normed algebra, and, when `A` is a C⋆-algebra, we show
that `𝓜(𝕜, A)` is also a C⋆-algebra. Moreover, in this case, for `a : 𝓜(𝕜, A)`,
`‖a‖ = ‖a.fst‖ = ‖a.snd‖`. -/


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedRing 𝓜(𝕜, A)
  body: NormedRing.induced _ _ (toProdMulOppositeHom : 𝓜(𝕜, A) ->+* (A ->L[𝕜] A) × (A ->L[𝕜] A)ᵐᵒᵖ)
    (by simpa using! toProdMulOpposite_injective)

中文:
实例 :
  签名: NormedRing 𝓜(𝕜, A)
  定义体: NormedRing.induced _ _ (toProdMulOppositeHom : 𝓜(𝕜, A) ->+* (A ->L[𝕜] A) × (A ->L[𝕜] A)ᵐᵒᵖ)
    (by simpa using! toProdMulOpposite_injective)

Depends on / 依赖: NormedRing, NormedRing.induced, induced, toProdMulOppositeHom, toProdMulOpposite_injective
-/
noncomputable instance : NormedRing 𝓜(𝕜, A) :=
  NormedRing.induced _ _ (toProdMulOppositeHom : 𝓜(𝕜, A) ->+* (A ->L[𝕜] A) × (A ->L[𝕜] A)ᵐᵒᵖ)
    (by simpa using! toProdMulOpposite_injective)

-- even though the definition is actually in terms of `DoubleCentralizer.toProdMulOpposite`, we
-- choose to see through that here to avoid `MulOpposite.op` appearing.
/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: (a : 𝓜(𝕜, A))
  statement: ‖a‖ = ‖toProdHom a‖
  proof: rfl

中文:
定理 norm_def
  条件: (a : 𝓜(𝕜, A))
  结论: ‖a‖ = ‖toProdHom a‖
  证明: rfl
-/
theorem norm_def (a : 𝓜(𝕜, A)) : ‖a‖ = ‖toProdHom a‖ :=
  rfl

/--
theorem `nnnorm_def` / 定理 `nnnorm_def`

English:
theorem nnnorm_def
  given: (a : 𝓜(𝕜, A))
  statement: ‖a‖₊ = ‖toProdHom a‖₊
  proof: rfl

中文:
定理 nnnorm_def
  条件: (a : 𝓜(𝕜, A))
  结论: ‖a‖₊ = ‖toProdHom a‖₊
  证明: rfl
-/
theorem nnnorm_def (a : 𝓜(𝕜, A)) : ‖a‖₊ = ‖toProdHom a‖₊ :=
  rfl

/--
theorem `norm_def'` / 定理 `norm_def'`

English:
theorem norm_def'
  given: (a : 𝓜(𝕜, A))
  statement: ‖a‖ = ‖toProdMulOppositeHom a‖
  proof: rfl

中文:
定理 norm_def'
  条件: (a : 𝓜(𝕜, A))
  结论: ‖a‖ = ‖toProdMulOppositeHom a‖
  证明: rfl
-/
theorem norm_def' (a : 𝓜(𝕜, A)) : ‖a‖ = ‖toProdMulOppositeHom a‖ :=
  rfl

/--
theorem `nnnorm_def'` / 定理 `nnnorm_def'`

English:
theorem nnnorm_def'
  given: (a : 𝓜(𝕜, A))
  statement: ‖a‖₊ = ‖toProdMulOppositeHom a‖₊
  proof: rfl

中文:
定理 nnnorm_def'
  条件: (a : 𝓜(𝕜, A))
  结论: ‖a‖₊ = ‖toProdMulOppositeHom a‖₊
  证明: rfl
-/
theorem nnnorm_def' (a : 𝓜(𝕜, A)) : ‖a‖₊ = ‖toProdMulOppositeHom a‖₊ :=
  rfl

/--
Instance `instNormedSpace` / 实例 `instNormedSpace`

English:
instance instNormedSpace
  signature: : NormedSpace 𝕜 𝓜(𝕜, A)
  body: { DoubleCentralizer.instModule with
    norm_smul_le := fun k a => (norm_smul_le k a.toProdMulOpposite :) }

中文:
实例 instNormedSpace
  签名: : NormedSpace 𝕜 𝓜(𝕜, A)
  定义体: { DoubleCentralizer.instModule with
    norm_smul_le := fun k a => (norm_smul_le k a.toProdMulOpposite :) }

Depends on / 依赖: DoubleCentralizer, DoubleCentralizer.instModule, a.toProdMulOpposite, instModule, norm_smul_le, toProdMulOpposite
-/
noncomputable instance instNormedSpace : NormedSpace 𝕜 𝓜(𝕜, A) :=
  { DoubleCentralizer.instModule with
    norm_smul_le := fun k a => (norm_smul_le k a.toProdMulOpposite :) }

/--
Instance `instNormedAlgebra` / 实例 `instNormedAlgebra`

English:
instance instNormedAlgebra
  signature: : NormedAlgebra 𝕜 𝓜(𝕜, A)
  body: { DoubleCentralizer.instAlgebra, DoubleCentralizer.instNormedSpace with }

中文:
实例 instNormedAlgebra
  签名: : NormedAlgebra 𝕜 𝓜(𝕜, A)
  定义体: { DoubleCentralizer.instAlgebra, DoubleCentralizer.instNormedSpace with }

Depends on / 依赖: DoubleCentralizer, DoubleCentralizer.instAlgebra, DoubleCentralizer.instNormedSpace, instAlgebra, instNormedSpace
-/
noncomputable instance instNormedAlgebra : NormedAlgebra 𝕜 𝓜(𝕜, A) :=
  { DoubleCentralizer.instAlgebra, DoubleCentralizer.instNormedSpace with }

/--
theorem `isUniformEmbedding_toProdMulOpposite` / 定理 `isUniformEmbedding_toProdMulOpposite`

English:
theorem isUniformEmbedding_toProdMulOpposite
  proof: isUniformEmbedding_comap toProdMulOpposite_injective

中文:
定理 isUniformEmbedding_toProdMulOpposite
  证明: isUniformEmbedding_comap toProdMulOpposite_injective
-/
theorem isUniformEmbedding_toProdMulOpposite :
    IsUniformEmbedding (toProdMulOpposite (𝕜 := 𝕜) (A := A)) :=
  isUniformEmbedding_comap toProdMulOpposite_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteSpace
  signature: A] : CompleteSpace 𝓜(𝕜, A)
  body: by
  rw [completeSpace_iff_isComplete_range isUniformEmbedding_toProdMulOpposite.isUniformInducing]
  apply IsClosed.isComplete
  simp only [range_toProdMulOpposite, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq (by fun_prop) (by fun_prop)

中文:
实例 [CompleteSpace
  签名: A] : CompleteSpace 𝓜(𝕜, A)
  定义体: by
  rw [completeSpace_iff_isComplete_range isUniformEmbedding_toProdMulOpposite.isUniformInducing]
  apply IsClosed.isComplete
  simp only [range_toProdMulOpposite, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq (by fun_prop) (by fun_prop)

Depends on / 依赖: IsClosed, IsClosed.isComplete, Set.ofPred_forall, completeSpace_iff_isComplete_range, fun_prop, isClosed_eq, isClosed_iInter, isComplete, isUniformEmbedding_toProdMulOpposite, isUniformEmbedding_toProdMulOpposite.isUniformInducing, isUniformInducing, ofPred_forall, range_toProdMulOpposite
-/
instance [CompleteSpace A] : CompleteSpace 𝓜(𝕜, A) := by
  rw [completeSpace_iff_isComplete_range isUniformEmbedding_toProdMulOpposite.isUniformInducing]
  apply IsClosed.isComplete
  simp only [range_toProdMulOpposite, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq (by fun_prop) (by fun_prop)

variable [StarRing A] [CStarRing A]

/--
theorem `norm_fst_eq_snd` / 定理 `norm_fst_eq_snd`

English:
theorem norm_fst_eq_snd
  given: (a : 𝓜(𝕜, A))
  statement: ‖a.fst‖ = ‖a.snd‖
  proof: by
  -- a handy lemma for this proof
  have h0 : forall f : A ->L[𝕜] A, forall C : Real>=0, (forall b : A, ‖f b‖₊ ^ 2 <= C * ‖f b‖₊ * ‖b‖₊) -> ‖f‖₊ <= C := by
    intro f C h
    have h1 b : C * ‖f b‖₊ * ‖b‖₊ <= C * ‖f‖₊ * ‖b‖₊ ^ 2 := by grw [f.le_opNNNorm b]; ring_nf; rfl
have := NNReal.div_le_of_l

中文:
定理 norm_fst_eq_snd
  条件: (a : 𝓜(𝕜, A))
  结论: ‖a.fst‖ = ‖a.snd‖
  证明: by
  -- a handy lemma for this proof
  have h0 : forall f : A ->L[𝕜] A, forall C : Real>=0, (forall b : A, ‖f b‖₊ ^ 2 <= C * ‖f b‖₊ * ‖b‖₊) -> ‖f‖₊ <= C := by
    intro f C h
    have h1 b : C * ‖f b‖₊ * ‖b‖₊ <= C * ‖f‖₊ * ‖b‖₊ ^ 2 := by grw [f.le_opNNNorm b]; ring_nf; rfl
have := NNReal.div_le_of_l
-/
theorem norm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fst‖ = ‖a.snd‖ := by
  -- a handy lemma for this proof
  have h0 : forall f : A ->L[𝕜] A, forall C : Real>=0, (forall b : A, ‖f b‖₊ ^ 2 <= C * ‖f b‖₊ * ‖b‖₊) -> ‖f‖₊ <= C := by
    intro f C h
    have h1 b : C * ‖f b‖₊ * ‖b‖₊ <= C * ‖f‖₊ * ‖b‖₊ ^ 2 := by grw [f.le_opNNNorm b]; ring_nf; rfl
have := NNReal.div_le_of_le_mul f.opNNNorm_le_bound _ by
simpa only [sqrt_sq, sqrt_mul] using fun b => sqrt_le_sqrt.2 (h b).trans (h1 b)
    convert! NNReal.rpow_le_rpow this two_pos.le
    · simp only [NNReal.rpow_two, div_pow, sq_sqrt]
      simp only [sq, mul_self_div_self]
    · simp only [NNReal.rpow_two, sq_sqrt]
  have h1 : forall b, ‖a.fst b‖₊ ^ 2 <= ‖a.snd‖₊ * ‖a.fst b‖₊ * ‖b‖₊ := by
    intro b
    calc
      ‖a.fst b‖₊ ^ 2 = ‖star (a.fst b) * a.fst b‖₊ := by
        simpa only [← sq] using CStarRing.nnnorm_star_mul_self.symm
      _ <= ‖a.snd (star (a.fst b))‖₊ * ‖b‖₊ := (a.central (star (a.fst b)) b ▸ nnnorm_mul_le _ _)
      _ <= ‖a.snd‖₊ * ‖a.fst b‖₊ * ‖b‖₊ :=
        nnnorm_star (a.fst b) ▸ mul_le_mul_left (a.snd.le_opNNNorm _) _
  have h2 : forall b, ‖a.snd b‖₊ ^ 2 <= ‖a.fst‖₊ * ‖a.snd b‖₊ * ‖b‖₊ := by
    intro b
    calc
      ‖a.snd b‖₊ ^ 2 = ‖a.snd b * star (a.snd b)‖₊ := by
        simpa only [← sq] using CStarRing.nnnorm_self_mul_star.symm
      _ <= ‖b‖₊ * ‖a.fst (star (a.snd b))‖₊ :=
        ((a.central b (star (a.snd b))).symm ▸ nnnorm_mul_le _ _)
      _ = ‖a.fst (star (a.snd b))‖₊ * ‖b‖₊ := mul_comm _ _
      _ <= ‖a.fst‖₊ * ‖a.snd b‖₊ * ‖b‖₊ :=
        nnnorm_star (a.snd b) ▸ mul_le_mul_left (a.fst.le_opNNNorm _) _
  exact le_antisymm (h0 _ _ h1) (h0 _ _ h2)

/--
theorem `nnnorm_fst_eq_snd` / 定理 `nnnorm_fst_eq_snd`

English:
theorem nnnorm_fst_eq_snd
  given: (a : 𝓜(𝕜, A))
  statement: ‖a.fst‖₊ = ‖a.snd‖₊
  proof: Subtype.ext norm_fst_eq_snd a

@[simp]

中文:
定理 nnnorm_fst_eq_snd
  条件: (a : 𝓜(𝕜, A))
  结论: ‖a.fst‖₊ = ‖a.snd‖₊
  证明: Subtype.ext norm_fst_eq_snd a

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, norm_fst_eq_snd
-/
theorem nnnorm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fst‖₊ = ‖a.snd‖₊ :=
Subtype.ext norm_fst_eq_snd a

@[simp]
/--
theorem `norm_fst` / 定理 `norm_fst`

English:
theorem norm_fst
  given: (a : 𝓜(𝕜, A))
  statement: ‖a.fst‖ = ‖a‖
  proof: by
  simp only [norm_def, toProdHom_apply, Prod.norm_def, norm_fst_eq_snd, max_eq_right le_rfl]

@[simp]

中文:
定理 norm_fst
  条件: (a : 𝓜(𝕜, A))
  结论: ‖a.fst‖ = ‖a‖
  证明: by
  simp only [norm_def, toProdHom_apply, Prod.norm_def, norm_fst_eq_snd, max_eq_right le_rfl]

@[simp]

Depends on / 依赖: Prod.norm_def, le_rfl, max_eq_right, norm_def, norm_fst_eq_snd, toProdHom_apply
-/
theorem norm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖ = ‖a‖ := by
  simp only [norm_def, toProdHom_apply, Prod.norm_def, norm_fst_eq_snd, max_eq_right le_rfl]

@[simp]
/--
theorem `norm_snd` / 定理 `norm_snd`

English:
theorem norm_snd
  given: (a : 𝓜(𝕜, A))
  statement: ‖a.snd‖ = ‖a‖
  proof: by rw [← norm_fst, norm_fst_eq_snd]

@[simp]

中文:
定理 norm_snd
  条件: (a : 𝓜(𝕜, A))
  结论: ‖a.snd‖ = ‖a‖
  证明: by rw [← norm_fst, norm_fst_eq_snd]

@[simp]

Depends on / 依赖: norm_fst, norm_fst_eq_snd
-/
theorem norm_snd (a : 𝓜(𝕜, A)) : ‖a.snd‖ = ‖a‖ := by rw [← norm_fst, norm_fst_eq_snd]

@[simp]
/--
theorem `nnnorm_fst` / 定理 `nnnorm_fst`

English:
theorem nnnorm_fst
  given: (a : 𝓜(𝕜, A))
  statement: ‖a.fst‖₊ = ‖a‖₊
  proof: Subtype.ext (norm_fst a)

@[simp]

中文:
定理 nnnorm_fst
  条件: (a : 𝓜(𝕜, A))
  结论: ‖a.fst‖₊ = ‖a‖₊
  证明: Subtype.ext (norm_fst a)

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, norm_fst
-/
theorem nnnorm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖₊ = ‖a‖₊ :=
  Subtype.ext (norm_fst a)

@[simp]
/--
theorem `nnnorm_snd` / 定理 `nnnorm_snd`

English:
theorem nnnorm_snd
  given: (a : 𝓜(𝕜, A))
  statement: ‖a.snd‖₊ = ‖a‖₊
  proof: Subtype.ext (norm_snd a)

中文:
定理 nnnorm_snd
  条件: (a : 𝓜(𝕜, A))
  结论: ‖a.snd‖₊ = ‖a‖₊
  证明: Subtype.ext (norm_snd a)

Depends on / 依赖: Subtype, Subtype.ext, norm_snd
-/
theorem nnnorm_snd (a : 𝓜(𝕜, A)) : ‖a.snd‖₊ = ‖a‖₊ :=
  Subtype.ext (norm_snd a)

end NontriviallyNormed

section DenselyNormed

variable {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜]
variable [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
variable [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [StarModule 𝕜 A]

/--
Instance `instCStarRing` / 实例 `instCStarRing`

English:
instance instCStarRing
  signature: : CStarRing 𝓜(𝕜, A) where
  body: fun (a : 𝓜(𝕜, A)) => le_of_eq Eq.symm congr_arg ((↑) : Real>=0 -> Real)
    show ‖star a * a‖₊ = ‖a‖₊ * ‖a‖₊ by
    /- The essence of the argument is this: let `a = (L,R)` and recall `‖a‖ = ‖L‖`.
    `star a = (star ∘ R ∘ star, star ∘ L ∘ star)`. Then for any `x y : A`, we have
    `‖star a * a‖ = ‖

中文:
实例 instCStarRing
  签名: : CStarRing 𝓜(𝕜, A) where
  定义体: fun (a : 𝓜(𝕜, A)) => le_of_eq Eq.symm congr_arg ((↑) : Real>=0 -> Real)
    show ‖star a * a‖₊ = ‖a‖₊ * ‖a‖₊ by
    /- The essence of the argument is this: let `a = (L,R)` and recall `‖a‖ = ‖L‖`.
    `star a = (star ∘ R ∘ star, star ∘ L ∘ star)`. Then for any `x y : A`, we have
    `‖star a * a‖ = ‖

Depends on / 依赖: Eq.symm, congr_arg, le_of_eq
-/
instance instCStarRing : CStarRing 𝓜(𝕜, A) where
norm_mul_self_le := fun (a : 𝓜(𝕜, A)) => le_of_eq Eq.symm congr_arg ((↑) : Real>=0 -> Real)
    show ‖star a * a‖₊ = ‖a‖₊ * ‖a‖₊ by
    /- The essence of the argument is this: let `a = (L,R)` and recall `‖a‖ = ‖L‖`.
    `star a = (star ∘ R ∘ star, star ∘ L ∘ star)`. Then for any `x y : A`, we have
    `‖star a * a‖ = ‖(star a * a).snd‖ = ‖R (star (L (star x))) * y‖ = ‖star (L (star x)) * L y‖`
    Now, on the one hand,
    `‖star (L (star x)) * L y‖ ≤ ‖star (L (star x))‖ * ‖L y‖ = ‖L (star x)‖ * ‖L y‖ ≤ ‖L‖ ^ 2`
    whenever `‖x‖, ‖y‖ ≤ 1`, so the supremum over all such `x, y` is at most `‖L‖ ^ 2`.
    On the other hand, for any `‖z‖ ≤ 1`, we may choose `x := star z` and `y := z` to get:
    `‖star (L (star x)) * L y‖ = ‖star (L z) * (L z)‖ = ‖L z‖ ^ 2`, and taking the supremum over
    all such `z` yields that the supremum is at least `‖L‖ ^ 2`. It is the latter part of the
    argument where `DenselyNormedField 𝕜` is required (for `sSup_unitClosedBall_eq_nnnorm`). -/
      have hball : (Metric.closedBall (0 : A) 1).Nonempty :=
        Metric.nonempty_closedBall.2 zero_le_one
      have key :
        forall x y, ‖x‖₊ <= 1 -> ‖y‖₊ <= 1 -> ‖a.snd (star (a.fst (star x))) * y‖₊ <= ‖a‖₊ * ‖a‖₊ := by
        intro x y hx hy
        rw [a.central]
        calc
          ‖star (a.fst (star x)) * a.fst y‖₊ <= ‖a.fst (star x)‖₊ * ‖a.fst y‖₊ :=
            nnnorm_star (a.fst (star x)) ▸ nnnorm_mul_le _ _
          _ <= ‖a.fst‖₊ * 1 * (‖a.fst‖₊ * 1) :=
            (mul_le_mul' (a.fst.le_opNorm_of_le ((nnnorm_star x).trans_le hx))
              (a.fst.le_opNorm_of_le hy))
          _ <= ‖a‖₊ * ‖a‖₊ := by simp only [mul_one, nnnorm_fst, le_rfl]
      rw [← nnnorm_snd]
      simp only [mul_snd, ← sSup_unitClosedBall_eq_nnnorm, star_snd, mul_apply_eq_comp]
      simp only [← @opNNNorm_mul_apply 𝕜 _ A]
      simp only [← sSup_unitClosedBall_eq_nnnorm, mul_apply']
      refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (hball.image _) ?_ fun r hr => ?_
      · rintro - ⟨x, hx, rfl⟩
        refine csSup_le (hball.image _) ?_
        rintro - ⟨y, hy, rfl⟩
        exact key x y (mem_closedBall_zero_iff.1 hx) (mem_closedBall_zero_iff.1 hy)
      · simp only [Set.mem_image, exists_exists_and_eq_and]
        have hr' : NNReal.sqrt r < ‖a‖₊ := ‖a‖₊.sqrt_mul_self ▸ NNReal.sqrt_lt_sqrt.2 hr
        simp_rw [← nnnorm_fst, ← sSup_unitClosedBall_eq_nnnorm] at hr'
        obtain ⟨_, ⟨x, hx, rfl⟩, hxr⟩ := exists_lt_of_lt_csSup (hball.image _) hr'
        have hx' : ‖x‖₊ <= 1 := mem_closedBall_zero_iff.1 hx
        refine ⟨star x, mem_closedBall_zero_iff.2 ((nnnorm_star x).trans_le hx'), ?_⟩
        refine lt_csSup_of_lt ?_ ⟨x, hx, rfl⟩ ?_
        · refine ⟨‖a‖₊ * ‖a‖₊, ?_⟩
          rintro - ⟨y, hy, rfl⟩
          exact key (star x) y ((nnnorm_star x).trans_le hx') (mem_closedBall_zero_iff.1 hy)
        · simpa [a.central, CStarRing.nnnorm_star_mul_self, ← sq]
            using pow_lt_pow_left₀ hxr zero_le two_ne_zero

end DenselyNormed

noncomputable instance {A : Type*} [NonUnitalCStarAlgebra A] : CStarAlgebra 𝓜(Complex, A) where

end DoubleCentralizer
