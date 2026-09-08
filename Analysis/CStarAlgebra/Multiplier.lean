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
for which we provide the localized notation `𝓜(𝕜, A)`.  A double centralizer is a pair of
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

/-- The type of *double centralizers*, also known as the *multiplier algebra* and denoted by
`𝓜(𝕜, A)`, of a non-unital normed algebra.

If `x : 𝓜(𝕜, A)`, then `x.fst` and `x.snd` are what is usually referred to as $L$ and $R$. -/
/-
**DoubleCentralizer** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u) →   (A : Type v) →     [inst : NontriviallyNormedField 𝕜] →  
     [inst_1 : NonUnitalNormedRing A] →         [inst_2 : NormedSpace 𝕜 A] → [SM
ulCommClass 𝕜 A A] → [IsScalarTower 𝕜 A A] → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of *double centralizers*, also known as the *multiplier algebra* and de
noted by
`𝓜(𝕜, A)`, of a non-unital normed algebra.

If `x : 𝓜(𝕜, A)`, then `x.fst` and `x.snd` are what is usually referred to as $L
$ and $R$.
-/
structure DoubleCentralizer (𝕜 : Type u) (A : Type v) [NontriviallyNormedField 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] extends
    (A →L[𝕜] A) × (A →L[𝕜] A) where
  /-- The centrality condition that the maps linear maps intertwine one another. -/
  central : ∀ x y : A, snd x * y = x * fst y

@[inherit_doc]
scoped[MultiplierAlgebra] notation "𝓜(" 𝕜 ", " A ")" => DoubleCentralizer 𝕜 A

open MultiplierAlgebra

@[ext]
/-
**DoubleCentralizer.ext** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DoubleCentralizer.ext (𝕜 : Type u) (A : Type v) [NontriviallyNormedField 𝕜
] [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower
 𝕜 A A] (a b : 𝓜(𝕜, A)) (h : a.toProd = b.toProd) : a = b
参数：𝕜 : Type u；A : Type v；a b : 𝓜(𝕜, A)；h : a.toProd = b.toProd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DoubleCentralizer.mk.injEq`：∀ {𝕜 : Type u} {A : Type v} [inst : Nontrivi
allyNormedField 𝕜] [inst_1 : NonUnitalNormedRing A]   [inst_2 : NormedSpace 𝕜 A]
 [inst_3 : SMulC…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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

/-
**DoubleCentralizer.range_toProd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：range_toProd : Set.range toProd = { lr : (A ->L[𝕜] A) × (A ->L[𝕜] A) | for
all x y, lr.2 x * y = x * lr.1 y }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `DoubleCentralizer.central`：∀ {𝕜 : Type u} {A : Type v} [inst : Nontrivia
llyNormedField 𝕜] [inst_1 : NonUnitalNormedRing A]   [inst_2 : NormedSpace 𝕜 A] 
[inst_3 : SMulC…
-/
theorem range_toProd :
    Set.range toProd = { lr : (A →L[𝕜] A) × (A →L[𝕜] A) | ∀ x y, lr.2 x * y = x * lr.1 y } :=
  Set.ext fun x =>
    ⟨by
      rintro ⟨a, rfl⟩
      exact a.central, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
/-
**DoubleCentralizer.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instAdd : Add 𝓜(𝕜, A) where add a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd : Add 𝓜(𝕜, A) where
  add a b :=
    { toProd := a.toProd + b.toProd
      central := fun x y =>
        show (a.snd + b.snd) x * y = x * (a.fst + b.fst) y by
          simp only [add_apply, mul_add, add_mul, central] }
/-
**DoubleCentralizer.instZero** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instZero : Zero 𝓜(𝕜, A) where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero 𝓜(𝕜, A) where
  zero :=
    { toProd := 0
      central := fun x y => (zero_mul y).trans (mul_zero x).symm }
/-
**DoubleCentralizer.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instNeg : Neg 𝓜(𝕜, A) where neg a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg : Neg 𝓜(𝕜, A) where
  neg a :=
    { toProd := -a.toProd
      central := fun x y =>
        show -a.snd x * y = x * -a.fst y by
          simp only [neg_mul, mul_neg, central] }
/-
**DoubleCentralizer.instSub** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instSub : Sub 𝓜(𝕜, A) where sub a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-
**DoubleCentralizer.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instSMul : SMul S 𝓜(𝕜, A) where smul s a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul S 𝓜(𝕜, A) where
  smul s a :=
    { toProd := s • a.toProd
      central := fun x y =>
        show (s • a.snd) x * y = x * (s • a.fst) y by
          simp only [smul_apply, mul_smul_comm, smul_mul_assoc, central] }

@[simp]
/-
**DoubleCentralizer.smul_toProd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：smul_toProd (s : S) (a : 𝓜(𝕜, A)) : (s • a).toProd = s • a.toProd
参数：s : S；a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_toProd (s : S) (a : 𝓜(𝕜, A)) : (s • a).toProd = s • a.toProd :=
  rfl
/-
**DoubleCentralizer.smul_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：smul_fst (s : S) (a : 𝓜(𝕜, A)) : (s • a).fst = s • a.fst
参数：s : S；a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_fst (s : S) (a : 𝓜(𝕜, A)) : (s • a).fst = s • a.fst :=
  rfl
/-
**DoubleCentralizer.smul_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：smul_snd (s : S) (a : 𝓜(𝕜, A)) : (s • a).snd = s • a.snd
参数：s : S；a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_snd (s : S) (a : 𝓜(𝕜, A)) : (s • a).snd = s • a.snd :=
  rfl

variable {T : Type*} [Monoid T] [DistribMulAction T A] [SMulCommClass 𝕜 T A]
  [ContinuousConstSMul T A] [IsScalarTower T A A] [SMulCommClass T A A]
/-
**DoubleCentralizer.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentraliz
er`。
形式化陈述：instIsScalarTower [SMul S T] [IsScalarTower S T A] : IsScalarTower S T 𝓜(𝕜
, A) where smul_assoc _ _ a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `DoubleCentralizer.ext`：DoubleCentralizer.ext (𝕜 : Type u) (A : Type v) [
NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommCl
ass 𝕜 A A] …
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance instIsScalarTower [SMul S T] [IsScalarTower S T A] : IsScalarTower S T 𝓜(𝕜, A) where
  smul_assoc _ _ a := ext (𝕜 := 𝕜) (A := A) _ _ <| smul_assoc _ _ a.toProd
/-
**DoubleCentralizer.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentraliz
er`。
形式化陈述：instSMulCommClass [SMulCommClass S T A] : SMulCommClass S T 𝓜(𝕜, A) where 
smul_comm _ _ a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `DoubleCentralizer.ext`：DoubleCentralizer.ext (𝕜 : Type u) (A : Type v) [
NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommCl
ass 𝕜 A A] …
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass [SMulCommClass S T A] : SMulCommClass S T 𝓜(𝕜, A) where
  smul_comm _ _ a := ext (𝕜 := 𝕜) (A := A) _ _ <| smul_comm _ _ a.toProd
/-
**DoubleCentralizer.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentral
izer`。
形式化陈述：instIsCentralScalar {R : Type*} [Semiring R] [Module R A] [SMulCommClass 𝕜
 R A] [ContinuousConstSMul R A] [IsScalarTower R A A] [SMulCommClass R A A] [Mod
ule Rᵐᵒᵖ A] [IsCentralScalar R A] : IsCentralScalar R 𝓜(𝕜, A) where op_smul_eq_s
mul _ a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul N α] [inst_2 : SMul Nᵐᵒᵖ α]   [IsCentralScalar N
 α] [SMulCom…
· 使用定理 `IsScalarTower.op_left`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [i
nst : SMul M α] [inst_1 : SMul Mᵐᵒᵖ α] [IsCentralScalar M α]   [inst_3 : SMul M 
N] [inst_4 …
· 使用定理 `SMulCommClass.op_left`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [i
nst : SMul M α] [inst_1 : SMul Mᵐᵒᵖ α] [IsCentralScalar M α]   [inst_3 : SMul N 
α] [SMulCom…
· 使用引理 `DoubleCentralizer.ext`：DoubleCentralizer.ext (𝕜 : Type u) (A : Type v) [
NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommCl
ass 𝕜 A A] …
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance instIsCentralScalar {R : Type*} [Semiring R] [Module R A] [SMulCommClass 𝕜 R A]
    [ContinuousConstSMul R A] [IsScalarTower R A A] [SMulCommClass R A A] [Module Rᵐᵒᵖ A]
    [IsCentralScalar R A] : IsCentralScalar R 𝓜(𝕜, A) where
  op_smul_eq_smul _ a := ext (𝕜 := 𝕜) (A := A) _ _ <| op_smul_eq_smul _ a.toProd

end Scalars

/-
**DoubleCentralizer.instOne** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instOne : One 𝓜(𝕜, A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne : One 𝓜(𝕜, A) :=
  ⟨⟨1, fun _x _y => rfl⟩⟩
/-
**DoubleCentralizer.instMul** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instMul : Mul 𝓜(𝕜, A) where mul a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul 𝓜(𝕜, A) where
  mul a b :=
    { toProd := (a.fst.comp b.fst, b.snd.comp a.snd)
      central := fun x y => show b.snd (a.snd x) * y = x * a.fst (b.fst y) by simp only [central] }
/-
**DoubleCentralizer.instNatCast** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instNatCast : NatCast 𝓜(𝕜, A) where natCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNatCast : NatCast 𝓜(𝕜, A) where
  natCast n :=
    ⟨n, fun x y => by
      rw [Prod.snd_natCast, Prod.fst_natCast]
      simp only [← Nat.smul_one_eq_cast, smul_apply, one_apply_eq_self, mul_smul_comm,
        smul_mul_assoc]⟩
/-
**DoubleCentralizer.instIntCast** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instIntCast : IntCast 𝓜(𝕜, A) where intCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIntCast : IntCast 𝓜(𝕜, A) where
  intCast n :=
    ⟨n, fun x y => by
      rw [Prod.snd_intCast, Prod.fst_intCast]
      simp only [← Int.smul_one_eq_cast, smul_apply, one_apply_eq_self, mul_smul_comm,
        smul_mul_assoc]⟩
/-
**DoubleCentralizer.instPow** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instPow : Pow 𝓜(𝕜, A) Nat where pow a n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPow : Pow 𝓜(𝕜, A) ℕ where
  pow a n :=
    ⟨a.toProd ^ n, fun x y => by
      induction n generalizing x y with
      | zero => rfl
      | succ k hk =>
        rw [Prod.pow_snd, Prod.pow_fst] at hk ⊢
        rw [pow_succ' a.snd, mul_apply_eq_comp, a.central, hk, pow_succ a.fst, mul_apply_eq_comp]⟩
/-
**DoubleCentralizer.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instInhabited : Inhabited 𝓜(𝕜, A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited 𝓜(𝕜, A) :=
  ⟨0⟩

@[simp]
/-
**DoubleCentralizer.add_toProd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：add_toProd (a b : 𝓜(𝕜, A)) : (a + b).toProd = a.toProd + b.toProd
参数：a b : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_toProd (a b : 𝓜(𝕜, A)) : (a + b).toProd = a.toProd + b.toProd :=
  rfl

@[simp]
/-
**DoubleCentralizer.zero_toProd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：zero_toProd : (0 : 𝓜(𝕜, A)).toProd = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_toProd : (0 : 𝓜(𝕜, A)).toProd = 0 :=
  rfl

@[simp]
/-
**DoubleCentralizer.neg_toProd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：neg_toProd (a : 𝓜(𝕜, A)) : (-a).toProd = -a.toProd
参数：a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_toProd (a : 𝓜(𝕜, A)) : (-a).toProd = -a.toProd :=
  rfl

@[simp]
/-
**DoubleCentralizer.sub_toProd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：sub_toProd (a b : 𝓜(𝕜, A)) : (a - b).toProd = a.toProd - b.toProd
参数：a b : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_toProd (a b : 𝓜(𝕜, A)) : (a - b).toProd = a.toProd - b.toProd :=
  rfl

@[simp]
/-
**DoubleCentralizer.one_toProd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：one_toProd : (1 : 𝓜(𝕜, A)).toProd = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_toProd : (1 : 𝓜(𝕜, A)).toProd = 1 :=
  rfl

@[simp]
/-
**DoubleCentralizer.natCast_toProd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`
。
形式化陈述：natCast_toProd (n : Nat) : (n : 𝓜(𝕜, A)).toProd = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_toProd (n : ℕ) : (n : 𝓜(𝕜, A)).toProd = n :=
  rfl

@[simp]
/-
**DoubleCentralizer.intCast_toProd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`
。
形式化陈述：intCast_toProd (n : Int) : (n : 𝓜(𝕜, A)).toProd = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intCast_toProd (n : ℤ) : (n : 𝓜(𝕜, A)).toProd = n :=
  rfl

@[simp]
/-
**DoubleCentralizer.pow_toProd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：pow_toProd (n : Nat) (a : 𝓜(𝕜, A)) : (a ^ n).toProd = a.toProd ^ n
参数：n : Nat；a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_toProd (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).toProd = a.toProd ^ n :=
  rfl
/-
**DoubleCentralizer.add_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：add_fst (a b : 𝓜(𝕜, A)) : (a + b).fst = a.fst + b.fst
参数：a b : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_fst (a b : 𝓜(𝕜, A)) : (a + b).fst = a.fst + b.fst :=
  rfl
/-
**DoubleCentralizer.add_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：add_snd (a b : 𝓜(𝕜, A)) : (a + b).snd = a.snd + b.snd
参数：a b : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_snd (a b : 𝓜(𝕜, A)) : (a + b).snd = a.snd + b.snd :=
  rfl
/-
**DoubleCentralizer.zero_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：zero_fst : (0 : 𝓜(𝕜, A)).fst = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_fst : (0 : 𝓜(𝕜, A)).fst = 0 :=
  rfl
/-
**DoubleCentralizer.zero_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：zero_snd : (0 : 𝓜(𝕜, A)).snd = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_snd : (0 : 𝓜(𝕜, A)).snd = 0 :=
  rfl
/-
**DoubleCentralizer.neg_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：neg_fst (a : 𝓜(𝕜, A)) : (-a).fst = -a.fst
参数：a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_fst (a : 𝓜(𝕜, A)) : (-a).fst = -a.fst :=
  rfl
/-
**DoubleCentralizer.neg_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：neg_snd (a : 𝓜(𝕜, A)) : (-a).snd = -a.snd
参数：a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_snd (a : 𝓜(𝕜, A)) : (-a).snd = -a.snd :=
  rfl
/-
**DoubleCentralizer.sub_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：sub_fst (a b : 𝓜(𝕜, A)) : (a - b).fst = a.fst - b.fst
参数：a b : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_fst (a b : 𝓜(𝕜, A)) : (a - b).fst = a.fst - b.fst :=
  rfl
/-
**DoubleCentralizer.sub_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：sub_snd (a b : 𝓜(𝕜, A)) : (a - b).snd = a.snd - b.snd
参数：a b : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_snd (a b : 𝓜(𝕜, A)) : (a - b).snd = a.snd - b.snd :=
  rfl
/-
**DoubleCentralizer.one_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：one_fst : (1 : 𝓜(𝕜, A)).fst = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_fst : (1 : 𝓜(𝕜, A)).fst = 1 :=
  rfl
/-
**DoubleCentralizer.one_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：one_snd : (1 : 𝓜(𝕜, A)).snd = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_snd : (1 : 𝓜(𝕜, A)).snd = 1 :=
  rfl

@[simp]
/-
**DoubleCentralizer.mul_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：mul_fst (a b : 𝓜(𝕜, A)) : (a * b).fst = a.fst * b.fst
参数：a b : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_fst (a b : 𝓜(𝕜, A)) : (a * b).fst = a.fst * b.fst :=
  rfl

@[simp]
/-
**DoubleCentralizer.mul_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：mul_snd (a b : 𝓜(𝕜, A)) : (a * b).snd = b.snd * a.snd
参数：a b : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_snd (a b : 𝓜(𝕜, A)) : (a * b).snd = b.snd * a.snd :=
  rfl
/-
**DoubleCentralizer.natCast_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：natCast_fst (n : Nat) : (n : 𝓜(𝕜, A)).fst = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_fst (n : ℕ) : (n : 𝓜(𝕜, A)).fst = n :=
  rfl
/-
**DoubleCentralizer.natCast_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：natCast_snd (n : Nat) : (n : 𝓜(𝕜, A)).snd = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_snd (n : ℕ) : (n : 𝓜(𝕜, A)).snd = n :=
  rfl
/-
**DoubleCentralizer.intCast_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：intCast_fst (n : Int) : (n : 𝓜(𝕜, A)).fst = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intCast_fst (n : ℤ) : (n : 𝓜(𝕜, A)).fst = n :=
  rfl
/-
**DoubleCentralizer.intCast_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：intCast_snd (n : Int) : (n : 𝓜(𝕜, A)).snd = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intCast_snd (n : ℤ) : (n : 𝓜(𝕜, A)).snd = n :=
  rfl
/-
**DoubleCentralizer.pow_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：pow_fst (n : Nat) (a : 𝓜(𝕜, A)) : (a ^ n).fst = a.fst ^ n
参数：n : Nat；a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_fst (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).fst = a.fst ^ n :=
  rfl
/-
**DoubleCentralizer.pow_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：pow_snd (n : Nat) (a : 𝓜(𝕜, A)) : (a ^ n).snd = a.snd ^ n
参数：n : Nat；a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_snd (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).snd = a.snd ^ n :=
  rfl

/-- The natural injection from `DoubleCentralizer.toProd` except the second coordinate inherits
`MulOpposite.op`. The ring structure on `𝓜(𝕜, A)` is the pullback under this map. -/
/-
**DoubleCentralizer.toProdMulOpposite** 是 Mathlib 中的一个定义，位于命名空间 `DoubleCentraliz
er`。
形式化陈述：toProdMulOpposite : 𝓜(𝕜, A) -> (A ->L[𝕜] A) × (A ->L[𝕜] A)ᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural injection from `DoubleCentralizer.toProd` except the second coordina
te inherits
`MulOpposite.op`. The ring structure on `𝓜(𝕜, A)` is the pullback under this map
.
-/
def toProdMulOpposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ := fun a =>
  (a.fst, MulOpposite.op a.snd)
/-
**DoubleCentralizer.toProdMulOpposite_injective** 是 Mathlib 中的一个定理，位于命名空间 `Doubl
eCentralizer`。
形式化陈述：toProdMulOpposite_injective : Function.Injective (toProdMulOpposite : 𝓜(𝕜,
 A) -> (A ->L[𝕜] A) × (A ->L[𝕜] A)ᵐᵒᵖ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用引理 `DoubleCentralizer.ext`：DoubleCentralizer.ext (𝕜 : Type u) (A : Type v) [
NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommCl
ass 𝕜 A A] …
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem toProdMulOpposite_injective :
    Function.Injective (toProdMulOpposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ) :=
  fun _a _b h =>
    let h' := Prod.ext_iff.mp h
    ext (𝕜 := 𝕜) (A := A) _ _ <| Prod.ext h'.1 <| MulOpposite.op_injective h'.2
/-
**DoubleCentralizer.range_toProdMulOpposite** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCen
tralizer`。
形式化陈述：range_toProdMulOpposite : Set.range toProdMulOpposite = { lr : (A ->L[𝕜] A
) × (A ->L[𝕜] A)ᵐᵒᵖ | forall x y, unop lr.2 x * y = x * lr.1 y }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `DoubleCentralizer.central`：∀ {𝕜 : Type u} {A : Type v} [inst : Nontrivia
llyNormedField 𝕜] [inst_1 : NonUnitalNormedRing A]   [inst_2 : NormedSpace 𝕜 A] 
[inst_3 : SMulC…
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
theorem range_toProdMulOpposite :
    Set.range toProdMulOpposite =
      { lr : (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ | ∀ x y, unop lr.2 x * y = x * lr.1 y } :=
  Set.ext fun x =>
    ⟨by
      rintro ⟨a, rfl⟩
      exact a.central, fun hx => ⟨⟨(x.1, unop x.2), hx⟩, Prod.ext rfl rfl⟩⟩

/-- The ring structure is inherited as the pullback under the injective map
`DoubleCentralizer.toProdMulOpposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ` -/
/-
**DoubleCentralizer.instRing** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instRing : Ring 𝓜(𝕜, A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DoubleCentralizer.toProdMulOpposite_injective`：toProdMulOpposite_injecti
ve : Function.Injective (toProdMulOpposite : 𝓜(𝕜, A) -> (A ->L[𝕜] A) × (A ->L[𝕜]
 A)ᵐᵒᵖ)

--- 原说明 ---
The ring structure is inherited as the pullback under the injective map
`DoubleCentralizer.toProdMulOpposite : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ`
-/
instance instRing : Ring 𝓜(𝕜, A) :=
  toProdMulOpposite_injective.ring _ rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _x _n => Prod.ext rfl <| MulOpposite.op_smul _ _)
    (fun _x _n => Prod.ext rfl <| MulOpposite.op_smul _ _)
    (fun _x _n => Prod.ext rfl <| MulOpposite.op_pow _ _) (fun _ => rfl) fun _ => rfl

/-- The canonical map `DoubleCentralizer.toProd` as an additive group homomorphism. -/
@[simps]
/-
**DoubleCentralizer.toProdHom** 是 Mathlib 中的一个定义，位于命名空间 `DoubleCentralizer`。
形式化陈述：toProdHom : 𝓜(𝕜, A) ->+ (A ->L[𝕜] A) × (A ->L[𝕜] A) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `DoubleCentralizer.toProd` as an additive group homomorphism.
-/
noncomputable def toProdHom : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A) where
  toFun := toProd
  map_zero' := rfl
  map_add' _x _y := rfl

/-- The canonical map `DoubleCentralizer.toProdMulOpposite` as a ring homomorphism. -/
@[simps]
/-
**DoubleCentralizer.toProdMulOppositeHom** 是 Mathlib 中的一个定义，位于命名空间 `DoubleCentra
lizer`。
形式化陈述：toProdMulOppositeHom : 𝓜(𝕜, A) ->+* (A ->L[𝕜] A) × (A ->L[𝕜] A)ᵐᵒᵖ where t
oFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `DoubleCentralizer.toProdMulOpposite` as a ring homomorphism.
-/
def toProdMulOppositeHom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ where
  toFun := toProdMulOpposite
  map_zero' := rfl
  map_one' := rfl
  map_add' _x _y := rfl
  map_mul' _x _y := rfl

/-- The module structure is inherited as the pullback under the additive group monomorphism
`DoubleCentralizer.toProd : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A)` -/
/-
**DoubleCentralizer.instModule** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instModule {S : Type*} [Semiring S] [Module S A] [SMulCommClass 𝕜 S A] [Co
ntinuousConstSMul S A] [IsScalarTower S A A] [SMulCommClass S A A] : Module S 𝓜(
𝕜, A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `DoubleCentralizer.ext`：DoubleCentralizer.ext (𝕜 : Type u) (A : Type v) [
NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommCl
ass 𝕜 A A] …

--- 原说明 ---
The module structure is inherited as the pullback under the additive group monom
orphism
`DoubleCentralizer.toProd : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A)`
-/
noncomputable instance instModule {S : Type*} [Semiring S] [Module S A] [SMulCommClass 𝕜 S A]
    [ContinuousConstSMul S A] [IsScalarTower S A A] [SMulCommClass S A A] : Module S 𝓜(𝕜, A) :=
  Function.Injective.module S toProdHom (ext (𝕜 := 𝕜) (A := A)) fun _x _y => rfl

-- TODO: generalize to `Algebra S 𝓜(𝕜, A)` once `ContinuousLinearMap.algebra` is generalized.
/-
**DoubleCentralizer.instAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instAlgebra : Algebra 𝕜 𝓜(𝕜, A) where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAlgebra : Algebra 𝕜 𝓜(𝕜, A) where
  algebraMap :=
  { toFun k :=
      { toProd := algebraMap 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A)) k
        central := fun x y => by
          simp_rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
            one_apply_eq_self, mul_smul_comm, smul_mul_assoc] }
    map_one' := ext (𝕜 := 𝕜) (A := A) _ _ <| map_one <| algebraMap 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A))
    map_mul' _ _ :=
      ext (𝕜 := 𝕜) (A := A) _ _ <|
        Prod.ext (map_mul (algebraMap 𝕜 (A →L[𝕜] A)) _ _)
          ((map_mul (algebraMap 𝕜 (A →L[𝕜] A)) _ _).trans (Algebra.commutes _ _))
    map_zero' := ext (𝕜 := 𝕜) (A := A) _ _ <| map_zero <| algebraMap 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A))
    map_add' _ _ := ext (𝕜 := 𝕜) (A := A) _ _ <|
      map_add (algebraMap 𝕜 ((A →L[𝕜] A) × (A →L[𝕜] A))) _ _ }
  commutes' _ _ := ext (𝕜 := 𝕜) (A := A) _ _ <|
    Prod.ext (Algebra.commutes _ _) (Algebra.commutes _ _).symm
  smul_def' _ _ := ext (𝕜 := 𝕜) (A := A) _ _ <|
    Prod.ext (Algebra.smul_def _ _) ((Algebra.smul_def _ _).trans <| Algebra.commutes _ _)

@[simp]
/-
**DoubleCentralizer.algebraMap_toProd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentraliz
er`。
形式化陈述：algebraMap_toProd (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).toProd = algebraMap 𝕜
 _ k
参数：k : 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_toProd (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).toProd = algebraMap 𝕜 _ k :=
  rfl
/-
**DoubleCentralizer.algebraMap_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`
。
形式化陈述：algebraMap_fst (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).fst = algebraMap 𝕜 _ k
参数：k : 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_fst (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).fst = algebraMap 𝕜 _ k :=
  rfl
/-
**DoubleCentralizer.algebraMap_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`
。
形式化陈述：algebraMap_snd (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).snd = algebraMap 𝕜 _ k
参数：k : 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_snd (k : 𝕜) : (algebraMap 𝕜 𝓜(𝕜, A) k).snd = algebraMap 𝕜 _ k :=
  rfl

/-!
### Star structure
-/


section Star

variable [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A]

/-- The star operation on `a : 𝓜(𝕜, A)` is given by
`(star a).toProd = (star ∘ a.snd ∘ star, star ∘ a.fst ∘ star)`. -/
/-
**DoubleCentralizer.instStar** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instStar : Star 𝓜(𝕜, A) where star a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The star operation on `a : 𝓜(𝕜, A)` is given by
`(star a).toProd = (star ∘ a.snd ∘ star, star ∘ a.fst ∘ star)`.
-/
instance instStar : Star 𝓜(𝕜, A) where
  star a :=
    { fst :=
        (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp a.snd).comp
          ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A)
      snd :=
        (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp a.fst).comp
          ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A)
      central := fun x y => by
        simpa only [star_mul, star_star]
          using! (congr_arg star (a.central (star y) (star x))).symm }

@[simp]
/-
**DoubleCentralizer.star_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：star_fst (a : 𝓜(𝕜, A)) (b : A) : (star a).fst b = star (a.snd (star b))
参数：a : 𝓜(𝕜, A)；b : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_fst (a : 𝓜(𝕜, A)) (b : A) : (star a).fst b = star (a.snd (star b)) :=
  rfl

@[simp]
/-
**DoubleCentralizer.star_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：star_snd (a : 𝓜(𝕜, A)) (b : A) : (star a).snd b = star (a.fst (star b))
参数：a : 𝓜(𝕜, A)；b : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_snd (a : 𝓜(𝕜, A)) (b : A) : (star a).snd b = star (a.fst (star b)) :=
  rfl
/-
**DoubleCentralizer.instStarAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentraliz
er`。
形式化陈述：instStarAddMonoid : StarAddMonoid 𝓜(𝕜, A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarAddMonoid : StarAddMonoid 𝓜(𝕜, A) :=
  { DoubleCentralizer.instStar with
    star_involutive _ := by ext <;> simp
    star_add _ _ := by ext <;> simp }
/-
**DoubleCentralizer.instStarRing** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instStarRing : StarRing 𝓜(𝕜, A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarRing : StarRing 𝓜(𝕜, A) :=
  { DoubleCentralizer.instStarAddMonoid with
    star_mul _ _ := by ext <;> simp }
/-
**DoubleCentralizer.instStarModule** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`
。
形式化陈述：instStarModule : StarModule 𝕜 𝓜(𝕜, A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `DoubleCentralizer.ext`：DoubleCentralizer.ext (𝕜 : Type u) (A : Type v) [
NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommCl
ass 𝕜 A A] …
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
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
/-
**DoubleCentralizer.coe** 是 Mathlib 中的一个定义，位于命名空间 `DoubleCentralizer`。
形式化陈述：(𝕜 : Type u_1) →   {A : Type u_2} →     [inst : NontriviallyNormedField 𝕜]
 →       [inst_1 : NonUnitalNormedRing A] →         [inst_2 : NormedSpace 𝕜 A] →
           [inst_3 : SMulCommClass 𝕜 A A] → [inst_4 : IsScalarTower 𝕜 A A] → A →
 DoubleCentralizer 𝕜 A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural coercion of `A` into `𝓜(𝕜, A)` given by sending `a : A` to the pair 
of linear
maps `Lₐ Rₐ : A →L[𝕜] A` given by left- and right-multiplication by `a`, respect
ively.

Warning: if `A = 𝕜`, then this is a coercion which is not definitionally equal t
o the
`algebraMap 𝕜 𝓜(𝕜, 𝕜)` coercion, but these are propositionally equal. See
`DoubleCentralizer.coe_eq_algebraMap` below.
-/
protected noncomputable def coe (a : A) : 𝓜(𝕜, A) :=
  { fst := ContinuousLinearMap.mul 𝕜 A a
    snd := (ContinuousLinearMap.mul 𝕜 A).flip a
    central := fun _x _y => mul_assoc _ _ _ }

/-- The natural coercion of `A` into `𝓜(𝕜, A)` given by sending `a : A` to the pair of linear
maps `Lₐ Rₐ : A →L[𝕜] A` given by left- and right-multiplication by `a`, respectively.

Warning: if `A = 𝕜`, then this is a coercion which is not definitionally equal to the
`algebraMap 𝕜 𝓜(𝕜, 𝕜)` coercion, but these are propositionally equal. See
`DoubleCentralizer.coe_eq_algebraMap` below. -/
/-
**DoubleCentralizer.** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural coercion of `A` into `𝓜(𝕜, A)` given by sending `a : A` to the pair 
of linear
maps `Lₐ Rₐ : A →L[𝕜] A` given by left- and right-multiplication by `a`, respect
ively.

Warning: if `A = 𝕜`, then this is a coercion which is not definitionally equal t
o the
`algebraMap 𝕜 𝓜(𝕜, 𝕜)` coercion, but these are propositionally equal. See
`DoubleCentralizer.coe_eq_algebraMap` below.
-/
noncomputable instance : CoeTC A 𝓜(𝕜, A) where
  coe := DoubleCentralizer.coe 𝕜

@[simp, norm_cast]
/-
**DoubleCentralizer.coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：coe_fst (a : A) : (a : 𝓜(𝕜, A)).fst = ContinuousLinearMap.mul 𝕜 A a
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fst (a : A) : (a : 𝓜(𝕜, A)).fst = ContinuousLinearMap.mul 𝕜 A a :=
  rfl

@[simp, norm_cast]
/-
**DoubleCentralizer.coe_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：coe_snd (a : A) : (a : 𝓜(𝕜, A)).snd = (ContinuousLinearMap.mul 𝕜 A).flip a
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_snd (a : A) : (a : 𝓜(𝕜, A)).snd = (ContinuousLinearMap.mul 𝕜 A).flip a :=
  rfl
/-
**DoubleCentralizer.coe_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentraliz
er`。
形式化陈述：coe_eq_algebraMap : (DoubleCentralizer.coe 𝕜 : 𝕜 -> 𝓜(𝕜, 𝕜)) = algebraMap 
𝕜 𝓜(𝕜, 𝕜)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `DoubleCentralizer.ext`：DoubleCentralizer.ext (𝕜 : Type u) (A : Type v) [
NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommCl
ass 𝕜 A A] …
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem coe_eq_algebraMap : (DoubleCentralizer.coe 𝕜 : 𝕜 → 𝓜(𝕜, 𝕜)) = algebraMap 𝕜 𝓜(𝕜, 𝕜) := by
  ext x : 3
  · rfl -- `fst` is defeq
  · refine ContinuousLinearMap.ext fun y => ?_
    exact mul_comm y x  -- `snd` multiplies on the wrong side

/-- The coercion of an algebra into its multiplier algebra as a non-unital star algebra
homomorphism. -/
@[simps]
/-
**DoubleCentralizer.coeHom** 是 Mathlib 中的一个定义，位于命名空间 `DoubleCentralizer`。
形式化陈述：coeHom [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A] : A 
->⋆ₙₐ[𝕜] 𝓜(𝕜, A) where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion of an algebra into its multiplier algebra as a non-unital star alge
bra
homomorphism.
-/
noncomputable def coeHom [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A] :
    A →⋆ₙₐ[𝕜] 𝓜(𝕜, A) where
  toFun a := a
  map_smul' _ _ := ext _ _ _ _ <| Prod.ext (map_smul _ _ _) (map_smul _ _ _)
  map_zero' := ext _ _ _ _ <| Prod.ext (map_zero _) (map_zero _)
  map_add' _ _ := ext _ _ _ _ <| Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_mul' _ _ := ext _ _ _ _ <| Prod.ext
    (ContinuousLinearMap.ext fun _ => (mul_assoc _ _ _))
    (ContinuousLinearMap.ext fun _ => (mul_assoc _ _ _).symm)
  map_star' _ := ext _ _ _ _ <| Prod.ext
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


/-- The normed group structure is inherited as the pullback under the ring monomorphism
`DoubleCentralizer.toProdMulOppositeHom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ`. -/
/-
**DoubleCentralizer.** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normed group structure is inherited as the pullback under the ring monomorph
ism
`DoubleCentralizer.toProdMulOppositeHom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐ
ᵒᵖ`.
-/
noncomputable instance : NormedRing 𝓜(𝕜, A) :=
  NormedRing.induced _ _ (toProdMulOppositeHom : 𝓜(𝕜, A) →+* (A →L[𝕜] A) × (A →L[𝕜] A)ᵐᵒᵖ)
    (by simpa using! toProdMulOpposite_injective)

-- even though the definition is actually in terms of `DoubleCentralizer.toProdMulOpposite`, we
-- choose to see through that here to avoid `MulOpposite.op` appearing.
/-
**DoubleCentralizer.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：norm_def (a : 𝓜(𝕜, A)) : ‖a‖ = ‖toProdHom a‖
参数：a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def (a : 𝓜(𝕜, A)) : ‖a‖ = ‖toProdHom a‖ :=
  rfl
/-
**DoubleCentralizer.nnnorm_def** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：nnnorm_def (a : 𝓜(𝕜, A)) : ‖a‖₊ = ‖toProdHom a‖₊
参数：a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nnnorm_def (a : 𝓜(𝕜, A)) : ‖a‖₊ = ‖toProdHom a‖₊ :=
  rfl
/-
**DoubleCentralizer.norm_def'** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：norm_def' (a : 𝓜(𝕜, A)) : ‖a‖ = ‖toProdMulOppositeHom a‖
参数：a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def' (a : 𝓜(𝕜, A)) : ‖a‖ = ‖toProdMulOppositeHom a‖ :=
  rfl
/-
**DoubleCentralizer.nnnorm_def'** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：nnnorm_def' (a : 𝓜(𝕜, A)) : ‖a‖₊ = ‖toProdMulOppositeHom a‖₊
参数：a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nnnorm_def' (a : 𝓜(𝕜, A)) : ‖a‖₊ = ‖toProdMulOppositeHom a‖₊ :=
  rfl
/-
**DoubleCentralizer.instNormedSpace** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer
`。
形式化陈述：instNormedSpace : NormedSpace 𝕜 𝓜(𝕜, A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instNormedSpace : NormedSpace 𝕜 𝓜(𝕜, A) :=
  { DoubleCentralizer.instModule with
    norm_smul_le := fun k a => (norm_smul_le k a.toProdMulOpposite :) }
/-
**DoubleCentralizer.instNormedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentraliz
er`。
形式化陈述：instNormedAlgebra : NormedAlgebra 𝕜 𝓜(𝕜, A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instNormedAlgebra : NormedAlgebra 𝕜 𝓜(𝕜, A) :=
  { DoubleCentralizer.instAlgebra, DoubleCentralizer.instNormedSpace with }
/-
**DoubleCentralizer.isUniformEmbedding_toProdMulOpposite** 是 Mathlib 中的一个定理，位于命名
空间 `DoubleCentralizer`。
形式化陈述：isUniformEmbedding_toProdMulOpposite : IsUniformEmbedding (toProdMulOpposi
te (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformEmbedding_comap`：isUniformEmbedding_comap {α : Type*} {β : Type
*} {f : α -> β} [u : UniformSpace β] (hf : Function.Injective f) : @IsUniformEmb
edding α β (Un…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `DoubleCentralizer.toProdMulOpposite_injective`：toProdMulOpposite_injecti
ve : Function.Injective (toProdMulOpposite : 𝓜(𝕜, A) -> (A ->L[𝕜] A) × (A ->L[𝕜]
 A)ᵐᵒᵖ)
-/
theorem isUniformEmbedding_toProdMulOpposite :
    IsUniformEmbedding (toProdMulOpposite (𝕜 := 𝕜) (A := A)) :=
  isUniformEmbedding_comap toProdMulOpposite_injective
/-
**DoubleCentralizer.** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompleteSpace A] : CompleteSpace 𝓜(𝕜, A) := by
  rw [completeSpace_iff_isComplete_range isUniformEmbedding_toProdMulOpposite.isUniformInducing]
  apply IsClosed.isComplete
  simp only [range_toProdMulOpposite, Set.ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_eq (by fun_prop) (by fun_prop)

variable [StarRing A] [CStarRing A]

/-- For `a : 𝓜(𝕜, A)`, the norms of `a.fst` and `a.snd` coincide, and hence these
also coincide with `‖a‖` which is `max (‖a.fst‖) (‖a.snd‖)`. -/
/-
**DoubleCentralizer.norm_fst_eq_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer
`。
形式化陈述：norm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fst‖ = ‖a.snd‖
参数：a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ContinuousLinearMap.le_opNNNorm`：le_opNNNorm (f : E ->SL[σ₁₂] F) (x : E)
 : ‖f x‖₊ <= ‖f‖₊ * ‖x‖₊
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.RingNF.mul_assoc_rev`：mul_assoc_rev (a b c : R) : a * (b 
* c) = a * b * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.RingNF.nat_rawCast_1`：nat_rawCast_1 : (Nat.rawCast 1 : R)
 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
For `a : 𝓜(𝕜, A)`, the norms of `a.fst` and `a.snd` coincide, and hence these
also coincide with `‖a‖` which is `max (‖a.fst‖) (‖a.snd‖)`.
-/
theorem norm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fst‖ = ‖a.snd‖ := by
  -- a handy lemma for this proof
  have h0 : ∀ f : A →L[𝕜] A, ∀ C : ℝ≥0, (∀ b : A, ‖f b‖₊ ^ 2 ≤ C * ‖f b‖₊ * ‖b‖₊) → ‖f‖₊ ≤ C := by
    intro f C h
    have h1 b : C * ‖f b‖₊ * ‖b‖₊ ≤ C * ‖f‖₊ * ‖b‖₊ ^ 2 := by grw [f.le_opNNNorm b]; ring_nf; rfl
    have := NNReal.div_le_of_le_mul <| f.opNNNorm_le_bound _ <| by
      simpa only [sqrt_sq, sqrt_mul] using fun b ↦ sqrt_le_sqrt.2 <| (h b).trans (h1 b)
    convert! NNReal.rpow_le_rpow this two_pos.le
    · simp only [NNReal.rpow_two, div_pow, sq_sqrt]
      simp only [sq, mul_self_div_self]
    · simp only [NNReal.rpow_two, sq_sqrt]
  have h1 : ∀ b, ‖a.fst b‖₊ ^ 2 ≤ ‖a.snd‖₊ * ‖a.fst b‖₊ * ‖b‖₊ := by
    intro b
    calc
      ‖a.fst b‖₊ ^ 2 = ‖star (a.fst b) * a.fst b‖₊ := by
        simpa only [← sq] using CStarRing.nnnorm_star_mul_self.symm
      _ ≤ ‖a.snd (star (a.fst b))‖₊ * ‖b‖₊ := (a.central (star (a.fst b)) b ▸ nnnorm_mul_le _ _)
      _ ≤ ‖a.snd‖₊ * ‖a.fst b‖₊ * ‖b‖₊ :=
        nnnorm_star (a.fst b) ▸ mul_le_mul_left (a.snd.le_opNNNorm _) _
  have h2 : ∀ b, ‖a.snd b‖₊ ^ 2 ≤ ‖a.fst‖₊ * ‖a.snd b‖₊ * ‖b‖₊ := by
    intro b
    calc
      ‖a.snd b‖₊ ^ 2 = ‖a.snd b * star (a.snd b)‖₊ := by
        simpa only [← sq] using CStarRing.nnnorm_self_mul_star.symm
      _ ≤ ‖b‖₊ * ‖a.fst (star (a.snd b))‖₊ :=
        ((a.central b (star (a.snd b))).symm ▸ nnnorm_mul_le _ _)
      _ = ‖a.fst (star (a.snd b))‖₊ * ‖b‖₊ := mul_comm _ _
      _ ≤ ‖a.fst‖₊ * ‖a.snd b‖₊ * ‖b‖₊ :=
        nnnorm_star (a.snd b) ▸ mul_le_mul_left (a.fst.le_opNNNorm _) _
  exact le_antisymm (h0 _ _ h1) (h0 _ _ h2)
/-
**DoubleCentralizer.nnnorm_fst_eq_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentraliz
er`。
形式化陈述：nnnorm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fst‖₊ = ‖a.snd‖₊
参数：a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `DoubleCentralizer.norm_fst_eq_snd`：norm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fs
t‖ = ‖a.snd‖
-/
theorem nnnorm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fst‖₊ = ‖a.snd‖₊ :=
  Subtype.ext <| norm_fst_eq_snd a

@[simp]
/-
**DoubleCentralizer.norm_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：norm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖ = ‖a‖
参数：a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DoubleCentralizer.norm_fst_eq_snd`：norm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fs
t‖ = ‖a.snd‖
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `DoubleCentralizer.toProdHom_apply`：∀ {𝕜 : Type u_1} {A : Type u_2} [inst
 : NontriviallyNormedField 𝕜] [inst_1 : NonUnitalNormedRing A]   [inst_2 : Norme
dSpace 𝕜 A] [inst_3 : S…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖ = ‖a‖ := by
  simp only [norm_def, toProdHom_apply, Prod.norm_def, norm_fst_eq_snd, max_eq_right le_rfl]

@[simp]
/-
**DoubleCentralizer.norm_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：norm_snd (a : 𝓜(𝕜, A)) : ‖a.snd‖ = ‖a‖
参数：a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DoubleCentralizer.norm_fst`：norm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖ = ‖a‖
· 使用定理 `DoubleCentralizer.norm_fst_eq_snd`：norm_fst_eq_snd (a : 𝓜(𝕜, A)) : ‖a.fs
t‖ = ‖a.snd‖
-/
theorem norm_snd (a : 𝓜(𝕜, A)) : ‖a.snd‖ = ‖a‖ := by rw [← norm_fst, norm_fst_eq_snd]

@[simp]
/-
**DoubleCentralizer.nnnorm_fst** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：nnnorm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖₊ = ‖a‖₊
参数：a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `DoubleCentralizer.norm_fst`：norm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖ = ‖a‖
-/
theorem nnnorm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖₊ = ‖a‖₊ :=
  Subtype.ext (norm_fst a)

@[simp]
/-
**DoubleCentralizer.nnnorm_snd** 是 Mathlib 中的一个定理，位于命名空间 `DoubleCentralizer`。
形式化陈述：nnnorm_snd (a : 𝓜(𝕜, A)) : ‖a.snd‖₊ = ‖a‖₊
参数：a : 𝓜(𝕜, A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `DoubleCentralizer.norm_snd`：norm_snd (a : 𝓜(𝕜, A)) : ‖a.snd‖ = ‖a‖
-/
theorem nnnorm_snd (a : 𝓜(𝕜, A)) : ‖a.snd‖₊ = ‖a‖₊ :=
  Subtype.ext (norm_snd a)

end NontriviallyNormed

section DenselyNormed

variable {𝕜 A : Type*} [DenselyNormedField 𝕜] [StarRing 𝕜]
variable [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
variable [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [StarModule 𝕜 A]

/-
**DoubleCentralizer.instCStarRing** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
形式化陈述：instCStarRing : CStarRing 𝓜(𝕜, A) where norm_mul_self_le
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.nonempty_closedBall`：nonempty_closedBall : (closedBall x ε).Nonem
pty ↔ 0 <= ε
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DoubleCentralizer.central`：∀ {𝕜 : Type u} {A : Type v} [inst : Nontrivia
llyNormedField 𝕜] [inst_1 : NonUnitalNormedRing A]   [inst_2 : NormedSpace 𝕜 A] 
[inst_3 : SMulC…
· 使用定理 `nnnorm_mul_le`：nnnorm_mul_le (a b : α) : ‖a * b‖₊ <= ‖a‖₊ * ‖b‖₊
· 使用定理 `nnnorm_star`：nnnorm_star (x : E) : ‖star x‖₊ = ‖x‖₊
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `ContinuousLinearMap.le_opNorm_of_le`：le_opNorm_of_le {c : Real} {x} (h :
 ‖x‖ <= c) : ‖f x‖ <= ‖f‖ * c
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DoubleCentralizer.nnnorm_fst`：nnnorm_fst (a : 𝓜(𝕜, A)) : ‖a.fst‖₊ = ‖a‖₊
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `DoubleCentralizer.nnnorm_snd`：nnnorm_snd (a : 𝓜(𝕜, A)) : ‖a.snd‖₊ = ‖a‖₊
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `mul_apply_eq_comp`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : Mul F} [self : IsMulApplyEqComp F α]   (f g : F) (x : α),
 (f * g…
· 使用定理 `ContinuousLinearMap.instIsMulApplyEqCompId`：∀ {R₁ : Type u_1} [inst : Se
miring R₁] {M₁ : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoi
d M₁]   [inst_3 : _root_.Module …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
（共 53 条，此处仅展示前 30 条）
-/
instance instCStarRing : CStarRing 𝓜(𝕜, A) where
  norm_mul_self_le := fun (a : 𝓜(𝕜, A)) => le_of_eq <| Eq.symm <| congr_arg ((↑) : ℝ≥0 → ℝ) <|
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
        ∀ x y, ‖x‖₊ ≤ 1 → ‖y‖₊ ≤ 1 → ‖a.snd (star (a.fst (star x))) * y‖₊ ≤ ‖a‖₊ * ‖a‖₊ := by
        intro x y hx hy
        rw [a.central]
        calc
          ‖star (a.fst (star x)) * a.fst y‖₊ ≤ ‖a.fst (star x)‖₊ * ‖a.fst y‖₊ :=
            nnnorm_star (a.fst (star x)) ▸ nnnorm_mul_le _ _
          _ ≤ ‖a.fst‖₊ * 1 * (‖a.fst‖₊ * 1) :=
            (mul_le_mul' (a.fst.le_opNorm_of_le ((nnnorm_star x).trans_le hx))
              (a.fst.le_opNorm_of_le hy))
          _ ≤ ‖a‖₊ * ‖a‖₊ := by simp only [mul_one, nnnorm_fst, le_rfl]
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
        have hx' : ‖x‖₊ ≤ 1 := mem_closedBall_zero_iff.1 hx
        refine ⟨star x, mem_closedBall_zero_iff.2 ((nnnorm_star x).trans_le hx'), ?_⟩
        refine lt_csSup_of_lt ?_ ⟨x, hx, rfl⟩ ?_
        · refine ⟨‖a‖₊ * ‖a‖₊, ?_⟩
          rintro - ⟨y, hy, rfl⟩
          exact key (star x) y ((nnnorm_star x).trans_le hx') (mem_closedBall_zero_iff.1 hy)
        · simpa [a.central, CStarRing.nnnorm_star_mul_self, ← sq]
            using pow_lt_pow_left₀ hxr zero_le two_ne_zero

end DenselyNormed

/-
**DoubleCentralizer.** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCentralizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {A : Type*} [NonUnitalCStarAlgebra A] : CStarAlgebra 𝓜(ℂ, A) where

end DoubleCentralizer

