/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.RootSystem.BaseChange
public import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear

/-!
# Nondegeneracy of the polarization on a finite root pairing

We show that if the base ring of a finite root pairing is linearly ordered, then the canonical
bilinear form is root-positive and positive-definite on the span of roots.
From these facts, it is easy to show that Coxeter weights in a finite root pairing are bounded
above by 4.  Thus, the pairings of roots and coroots in a root pairing are restricted to the
interval `[-4, 4]`.  Furthermore, a linearly independent pair of roots cannot have Coxeter weight 4.
For the case of crystallographic root pairings, we are thus reduced to a finite set of possible
options for each pair.
Another application is to the faithfulness of the Weyl group action on roots, and finiteness of the
Weyl group.

## Main results:
* `RootPairing.IsAnisotropic`: We say a finite root pairing is anisotropic if there are no roots /
  coroots which have length zero w.r.t. the root / coroot forms.
* `RootPairing.rootForm_pos_of_nonzero`: `RootForm` is strictly positive on non-zero linear
  combinations of roots. This gives us a convenient way to eliminate certain Dynkin diagrams from
  the classification, since it suffices to produce a nonzero linear combination of simple roots with
  non-positive norm.
* `RootPairing.rootForm_restrict_nondegenerate_of_ordered`: The root form is non-degenerate if
  the coefficients are ordered.
* `RootPairing.rootForm_restrict_nondegenerate_of_isAnisotropic`: the root form is
  non-degenerate if the coefficients are a field and the pairing is crystallographic.

## References:
* [N. Bourbaki, *Lie groups and Lie algebras. Chapters 4--6*][bourbaki1968]
* [M. Demazure, *SGA III, Exposé XXI, Données Radicielles*][demazure1970]

## Todo
* Weyl-invariance of `RootForm` and `CorootForm`
* Faithfulness of Weyl group perm action, and finiteness of Weyl group, over ordered rings.
* Relation to Coxeter weight.
-/

@[expose] public section

noncomputable section

open Set Function
open Module hiding reflection
open Submodule (span)

namespace RootPairing

variable {ι R M N : Type*} [Fintype ι] [AddCommGroup M] [AddCommGroup N]

section CommRing

variable [CommRing R] [Module R M] [Module R N] (P : RootPairing ι R M N)

/-- We say a finite root pairing is anisotropic if there are no roots / coroots which have length
zero w.r.t. the root / coroot forms.

Examples include crystallographic pairings in characteristic zero
`RootPairing.instIsAnisotropicOfIsCrystallographic` and pairings over ordered scalars.
`RootPairing.instIsAnisotropicOfLinearOrderedCommRing`. -/
/-
**RootPairing.IsAnisotropic** 是 Mathlib 中的一个归纳类型，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [Fintype ι] →           [inst : AddCommGroup M] →             [ins
t_1 : AddCommGroup N] →               [inst_2 : CommRing R] →                 [i
nst_3 : _root_.Module R M] → [inst_4 : _root_.Module R N] → RootPairing ι R M N 
→ Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say a finite root pairing is anisotropic if there are no roots / coroots whic
h have length
zero w.r.t. the root / coroot forms.

Examples include crystallographic pairings in characteristic zero
`RootPairing.instIsAnisotropicOfIsCrystallographic` and pairings over ordered sc
alars.
`RootPairing.instIsAnisotropicOfLinearOrderedCommRing`.
-/
class IsAnisotropic : Prop where
  rootForm_root_ne_zero (i : ι) : P.RootForm (P.root i) (P.root i) ≠ 0
  corootForm_coroot_ne_zero (i : ι) : P.CorootForm (P.coroot i) (P.coroot i) ≠ 0
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsAnisotropic] : P.flip.IsAnisotropic where
  rootForm_root_ne_zero := IsAnisotropic.corootForm_coroot_ne_zero
  corootForm_coroot_ne_zero := IsAnisotropic.rootForm_root_ne_zero (P := P)
/-
**RootPairing.isAnisotropic_of_isValuedIn** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing
`。
形式化陈述：isAnisotropic_of_isValuedIn (S : Type*) [CommRing S] [LinearOrder S] [IsSt
rictOrderedRing S] [Algebra S R] [FaithfulSMul S R] [P.IsValuedIn S] : IsAnisotr
opic P where rootForm_root_ne_zero i
参数：S : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.RootPositiveForm.form_apply_root_ne_zero`：form_apply_root_ne
_zero (i : ι) : B.form (P.root i) (P.root i) != 0
· 使用定理 `RootPairing.instIsValuedInFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
-/
lemma isAnisotropic_of_isValuedIn (S : Type*)
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    [Algebra S R] [FaithfulSMul S R] [P.IsValuedIn S] :
    IsAnisotropic P where
  rootForm_root_ne_zero i := (P.posRootForm S).form_apply_root_ne_zero i
  corootForm_coroot_ne_zero i := (P.flip.posRootForm S).form_apply_root_ne_zero i
/-
**RootPairing.instIsAnisotropicOfIsCrystallographic** 是 Mathlib 中的一个实例，位于命名空间 `R
ootPairing`。
形式化陈述：instIsAnisotropicOfIsCrystallographic [CharZero R] [P.IsCrystallographic] 
: IsAnisotropic P
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.isAnisotropic_of_isValuedIn`：isAnisotropic_of_isValuedIn (S 
: Type*) [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] [Algebra S R] [Fai
thfulSMul S R] [P.IsValuedIn …
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
-/
instance instIsAnisotropicOfIsCrystallographic [CharZero R] [P.IsCrystallographic] :
    IsAnisotropic P :=
  P.isAnisotropic_of_isValuedIn ℤ

/-- The root form of an anisotropic pairing as an invariant form. -/
/-
**RootPairing.toInvariantForm** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : Fintype ι] →           [inst_1 : AddCommGroup M] →        
     [inst_2 : AddCommGroup N] →               [inst_3 : CommRing R] →          
       [inst_4 : _root_.Module R M] →                   [inst_5 : _root_.Module 
R N] → (P : RootPairing ι R M N) → [P.IsAnisotropic] → P.InvariantForm
参数：P : RootPairing ι R M N。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.rootForm_symmetric`：rootForm_symmetric : LinearMap.IsSymm P.
RootForm
· 使用定理 `RootPairing.IsAnisotropic.rootForm_root_ne_zero`：∀ {ι : Type u_1} {R : T
ype u_2} {M : Type u_3} {N : Type u_4} {inst : Fintype ι} {inst_1 : AddCommGroup
 M}   {inst_2 : AddCommGroup N} {inst…
· 使用引理 `RootPairing.rootForm_reflection_reflection_apply`：rootForm_reflection_re
flection_apply (i : ι) (x y : M) : P.RootForm (P.reflection i x) (P.reflection i
 y) = P.RootForm x y

--- 原说明 ---
The root form of an anisotropic pairing as an invariant form.
-/
@[simps] def toInvariantForm [P.IsAnisotropic] : P.InvariantForm where
  form := P.RootForm
  symm := P.rootForm_symmetric
  ne_zero := IsAnisotropic.rootForm_root_ne_zero
  isOrthogonal_reflection := P.rootForm_reflection_reflection_apply
/-
**RootPairing.smul_coroot_eq_of_root_add_root_eq** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing`。
形式化陈述：smul_coroot_eq_of_root_add_root_eq [P.IsAnisotropic] [IsDomain R] [IsTorsi
onFree R N] {i j k : ι} {m n : R} (hk : m • P.root i + n • P.root j = P.root k) 
: letI Q
参数：hk : m • P.root i + n • P.root j = P.root k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.rootForm_self_smul_coroot`：rootForm_self_smul_coroot (i : ι)
 : (P.RootForm (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root 
i)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `nsmul_add`：∀ {M : Type u_4} [inst : AddCommMonoid M] (a b : M) (n : ℕ), 
n • (a + b) = n • a + n • b
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B 
: M →ₛₗ[I…
· 使用引理 `RootPairing.rootForm_symmetric`：rootForm_symmetric : LinearMap.IsSymm P.
RootForm
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.toInvariantForm_form`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup M]   [inst_2 :
 AddCommGroup N] [inst…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
（共 70 条，此处仅展示前 30 条）
-/
lemma smul_coroot_eq_of_root_add_root_eq [P.IsAnisotropic] [IsDomain R] [IsTorsionFree R N]
    {i j k : ι} {m n : R} (hk : m • P.root i + n • P.root j = P.root k) :
    letI Q :=
      (m * m) * P.pairing i j + (m * n) * (P.pairing i j * P.pairing j i) + (n * n) * P.pairing j i
    Q • P.coroot k = m • P.pairing i j • P.coroot i + n • P.pairing j i • P.coroot j := by
  let B := P.toInvariantForm
  let lsq (i) : R := B.form (P.root i) (P.root i)
  have hlsq (i : ι) : lsq i = P.RootForm (P.root i) (P.root i) := rfl
  have h₁ : lsq k • P.coroot k = (m • lsq i) • P.coroot i + (n • lsq j) • P.coroot j := by
    simp only [hlsq, smul_assoc, P.rootForm_self_smul_coroot, smul_comm _ 2]
    rw [← map_smul _ m, ← map_smul _ n, ← nsmul_add, ← map_add, hk]
  have h₂ :
      lsq k = (m * m) * lsq i + (m * n) * (2 * B.form (P.root i) (P.root j)) + (n * n) * lsq j := by
    have aux : P.RootForm (P.root j) (P.root i) = B.form (P.root i) (P.root j) :=
      P.rootForm_symmetric.eq (P.root j) (P.root i)
    simp [hlsq, ← hk, aux, B]
    ring
  have h₃ : 2 * B.form (P.root i) (P.root j) = P.pairing i j * lsq j :=
    B.two_mul_apply_root_root i j
  have h₄ : P.pairing j i * lsq i = P.pairing i j * lsq j := B.pairing_mul_eq_pairing_mul_swap i j
  replace h₁ :
      (m * m * (P.pairing j i * lsq i)) • P.coroot k +
      (m * n * (P.pairing j i * P.pairing i j * lsq j)) • P.coroot k +
      (n * n * (P.pairing j i * lsq j)) • P.coroot k =
        (m * (P.pairing j i * lsq i)) • P.coroot i +
        (n * (P.pairing j i * lsq j)) • P.coroot j := by
    rw [h₂, h₃] at h₁
    replace h₁ := congr_arg (fun n ↦ P.pairing j i • n) h₁
    simp only [add_smul, smul_add, ← mul_smul, smul_eq_mul] at h₁
    convert! h₁ using 1
    · module
    · ring_nf
  simp only [h₄] at h₁
  apply smul_right_injective _ (r := lsq j) (RootPairing.IsAnisotropic.rootForm_root_ne_zero j)
  simp only
  convert! h₁ using 1
  · module
  · module

section DomainAlg

variable (S : Type*) [CommRing S] [IsDomain R] [IsDomain S] [Algebra S R] [FaithfulSMul S R]
  [P.IsValuedIn S] [Module S M] [IsScalarTower S R M] [Module S N] [IsScalarTower S R N]

/-
**RootPairing.finrank_range_polarization_eq_finrank_span_coroot** 是 Mathlib 中的一个
引理，位于命名空间 `RootPairing`。
形式化陈述：finrank_range_polarization_eq_finrank_span_coroot [P.IsAnisotropic] : finr
ank S (LinearMap.range (P.PolarizationIn S)) = finrank S (P.corootSpan S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Submodule.finrank_mono`：Submodule.finrank_mono {s t : Submodule R M} [Mo
dule.Finite R t] (hst : s <= t) : finrank R s <= finrank R t
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `RootPairing.instFiniteSubtypeMemSubmoduleCorootSpanOfFinite`：∀ {ι : Type
 u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 :
 AddCommGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `RootPairing.range_polarizationIn_le_span_coroot`：range_polarizationIn_le
_span_coroot : LinearMap.range (P.PolarizationIn S) <= P.corootSpan S
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用引理 `Module.IsTorsionFree.trans_faithfulSMul`：Module.IsTorsionFree.trans_fait
hfulSMul [Nontrivial R] [IsCancelMulZero A] [AddCommMonoid M] [Module A M] [Modu
le R M] [IsTorsionFree A M] […
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `FaithfulSMul.algebraMap_eq_zero_iff`：algebraMap_eq_zero_iff {r : R} : al
gebraMap R A r = 0 ↔ r = 0
· 使用定理 `RootPairing.IsAnisotropic.rootForm_root_ne_zero`：∀ {ι : Type u_1} {R : T
ype u_2} {M : Type u_3} {N : Type u_4} {inst : Fintype ι} {inst_1 : AddCommGroup
 M}   {inst_2 : AddCommGroup N} {inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.algebraMap_rootFormIn`：algebraMap_rootFormIn (x y : P.rootSp
an S) : (algebraMap S R) (P.RootFormIn S x y) = P.RootForm x y
· 使用定理 `LinearMap.finrank_le_of_isSMulRegular`：LinearMap.finrank_le_of_isSMulReg
ular {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R 
M] (L L' : Submodule R M) […
· 使用定理 `RootPairing.instFiniteSubtypeMemSubmoduleRootSpanOfFinite`：∀ {ι : Type u
_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : A
ddCommGroup M]   [inst_2 : _root_.Module R M] […
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_range_iff_exists_fun`：Submodule.mem_span_range_iff_ex
ists_fun : x in span R (range v) ↔ exists c : α -> R, ∑ i, c i • v i = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
（共 32 条，此处仅展示前 30 条）
-/
lemma finrank_range_polarization_eq_finrank_span_coroot [P.IsAnisotropic] :
    finrank S (LinearMap.range (P.PolarizationIn S)) = finrank S (P.corootSpan S) := by
  apply (Submodule.finrank_mono (P.range_polarizationIn_le_span_coroot S)).antisymm
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : Module.IsTorsionFree S N := .trans_faithfulSMul S R N
  have h_ne : ∏ i, (P.RootFormIn S (P.rootSpanMem S i) (P.rootSpanMem S i)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ h ↦ ?_
    have := (FaithfulSMul.algebraMap_eq_zero_iff S R).mpr h
    rw [algebraMap_rootFormIn] at this
    apply IsAnisotropic.rootForm_root_ne_zero i this
  refine LinearMap.finrank_le_of_isSMulRegular (P.corootSpan S)
    (LinearMap.range (M₂ := N) (P.PolarizationIn S))
    (smul_right_injective N h_ne) ?_
  intro _ hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hx
  rw [← hc, Finset.smul_sum]
  simp_rw [smul_smul, mul_comm, ← smul_smul]
  exact Submodule.sum_smul_mem (LinearMap.range (P.PolarizationIn S)) c
    fun j _ ↦ prod_rootFormIn_smul_coroot_mem_range_PolarizationIn P S j

/-- An auxiliary lemma en route to `RootPairing.finrank_corootSpan_eq`. -/
/-
**RootPairing.finrank_corootSpan_le** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary lemma en route to `RootPairing.finrank_corootSpan_eq`.
-/
private lemma finrank_corootSpan_le [P.IsAnisotropic] :
    finrank S (P.corootSpan S) ≤ finrank S (P.rootSpan S) := by
  rw [← finrank_range_polarization_eq_finrank_span_coroot]
  exact LinearMap.finrank_range_le (P.PolarizationIn S)
/-
**RootPairing.finrank_corootSpan_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：finrank_corootSpan_eq [P.IsAnisotropic] : finrank S (P.corootSpan S) = fin
rank S (P.rootSpan S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `_private.Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate.0.RootPai
ring.finrank_corootSpan_le`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : 
Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGroup 
N] [inst…
· 使用定理 `RootPairing.instIsValuedInFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
· 使用定理 `RootPairing.instIsAnisotropicFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_3} {N : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup M]   [inst_2 
: AddCommGroup N] [inst…
-/
lemma finrank_corootSpan_eq [P.IsAnisotropic] :
    finrank S (P.corootSpan S) = finrank S (P.rootSpan S) :=
  le_antisymm (P.finrank_corootSpan_le S) (P.flip.finrank_corootSpan_le S)
/-
**RootPairing.polarizationIn_Injective** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：polarizationIn_Injective [P.IsAnisotropic] : Function.Injective (P.Polariz
ationIn S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用引理 `Module.IsTorsionFree.trans_faithfulSMul`：Module.IsTorsionFree.trans_fait
hfulSMul [Nontrivial R] [IsCancelMulZero A] [AddCommMonoid M] [Module A M] [Modu
le R M] [IsTorsionFree A M] […
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `top_disjoint`：top_disjoint : Disjoint ⊤ a ↔ a = ⊥
· 使用引理 `Submodule.disjoint_ker_of_finrank_le`：Submodule.disjoint_ker_of_finrank_
le [IsDomain R] [IsTorsionFree R M] {N : Type*} [AddCommGroup N] [Module R N] {L
 : Submodule R M} [Module.…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…
· 使用定理 `RootPairing.instFiniteSubtypeMemSubmoduleRootSpanOfFinite`：∀ {ι : Type u
_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : A
ddCommGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用引理 `RootPairing.finrank_corootSpan_eq`：finrank_corootSpan_eq [P.IsAnisotropi
c] : finrank S (P.corootSpan S) = finrank S (P.rootSpan S)
· 使用引理 `RootPairing.finrank_range_polarization_eq_finrank_span_coroot`：finrank_r
ange_polarization_eq_finrank_span_coroot [P.IsAnisotropic] : finrank S (LinearMa
p.range (P.PolarizationIn S)) = finrank S (P.coroot…
· 使用定理 `Submodule.finrank_mono`：Submodule.finrank_mono {s t : Submodule R M} [Mo
dule.Finite R t] (hst : s <= t) : finrank R s <= finrank R t
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
-/
lemma polarizationIn_Injective [P.IsAnisotropic] :
    Function.Injective (P.PolarizationIn S) := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsTorsionFree S M := .trans_faithfulSMul S R M
  rw [← LinearMap.ker_eq_bot, ← top_disjoint]
  refine Submodule.disjoint_ker_of_finrank_le (L := ⊤) (P.PolarizationIn S) ?_
  rw [finrank_top, ← finrank_corootSpan_eq, ← finrank_range_polarization_eq_finrank_span_coroot]
  exact Submodule.finrank_mono <| le_of_eq <| LinearMap.range_eq_map (P.PolarizationIn S)
/-
**RootPairing.exists_coroot_ne** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：exists_coroot_ne [P.IsAnisotropic] {x : P.rootSpan S} (hx : x != 0) : exis
ts i, P.coroot'In S i x != 0
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.polarizationIn_Injective`：polarizationIn_Injective [P.IsAnis
otropic] : Function.Injective (P.PolarizationIn S)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fintype.sum_eq_zero`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] 
[inst_1 : AddCommMonoid M] (f : α → M),   (∀ (a : α), f a = 0) → ∑ a, f a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RootPairing.PolarizationIn_apply`：PolarizationIn_apply (x : P.rootSpan S
) : P.PolarizationIn S x = ∑ i, P.coroot'In S i x • P.coroot i
-/
lemma exists_coroot_ne [P.IsAnisotropic]
    {x : P.rootSpan S} (hx : x ≠ 0) :
    ∃ i, P.coroot'In S i x ≠ 0 := by
  have hI := P.polarizationIn_Injective S
  have h := (map_ne_zero_iff (P.PolarizationIn S) hI).mpr hx
  rw [PolarizationIn_apply] at h
  contrapose! h
  exact Fintype.sum_eq_zero (fun a ↦ (P.coroot'In S a) x • P.coroot a) fun i ↦ by simp [h i]

end DomainAlg

section LinearOrderedCommRingAlg

variable (S : Type*) [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] [IsDomain R] [Algebra S R]
  [FaithfulSMul S R] [P.IsValuedIn S] [Module S M] [IsScalarTower S R M] [Module S N]
  [IsScalarTower S R N]

/-
**RootPairing.posRootForm_posForm_pos_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Root
Pairing`。
形式化陈述：posRootForm_posForm_pos_of_ne_zero {x : P.rootSpan S} (hx : x != 0) : 0 < 
(P.posRootForm S).posForm x x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.posRootForm_posForm_apply_apply`：posRootForm_posForm_apply_a
pply (x y : P.rootSpan S) : (P.posRootForm S).posForm x y = ∑ i, P.coroot'In S i
 x * P.coroot'In S i y
· 使用引理 `RootPairing.isAnisotropic_of_isValuedIn`：isAnisotropic_of_isValuedIn (S 
: Type*) [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] [Algebra S R] [Fai
thfulSMul S R] [P.IsValuedIn …
· 使用引理 `RootPairing.exists_coroot_ne`：exists_coroot_ne [P.IsAnisotropic] {x : P.
rootSpan S} (hx : x != 0) : exists i, P.coroot'In S i x != 0
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Finset.sum_pos'`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι
} [Ad…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem posRootForm_posForm_pos_of_ne_zero {x : P.rootSpan S} (hx : x ≠ 0) :
    0 < (P.posRootForm S).posForm x x := by
  rw [posRootForm_posForm_apply_apply]
  have := P.isAnisotropic_of_isValuedIn S
  have : ∃ i ∈ Finset.univ, 0 < (P.coroot'In S i) x * (P.coroot'In S i) x := by
    obtain ⟨i, hi⟩ := P.exists_coroot_ne S hx
    use i
    exact ⟨Finset.mem_univ i, mul_self_pos.mpr hi⟩
  exact Finset.sum_pos' (fun i a ↦ mul_self_nonneg ((P.coroot'In S i) x)) this
/-
**RootPairing.posRootForm_rootFormIn_posDef** 是 Mathlib 中的一个引理，位于命名空间 `RootPairi
ng`。
形式化陈述：posRootForm_rootFormIn_posDef : (P.RootFormIn S).toQuadraticMap.PosDef
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.posRootForm_eq`：posRootForm_eq : (P.posRootForm S).posForm =
 P.RootFormIn S
· 使用定理 `RootPairing.posRootForm_posForm_pos_of_ne_zero`：posRootForm_posForm_pos_
of_ne_zero {x : P.rootSpan S} (hx : x != 0) : 0 < (P.posRootForm S).posForm x x
-/
lemma posRootForm_rootFormIn_posDef : (P.RootFormIn S).toQuadraticMap.PosDef := by
  intro x hx
  simpa using P.posRootForm_posForm_pos_of_ne_zero S hx
/-
**RootPairing.posRootForm_posForm_anisotropic** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring`。
形式化陈述：posRootForm_posForm_anisotropic : (P.posRootForm S).posForm.toQuadraticMap
.Anisotropic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `RootPairing.posRootForm_posForm_pos_of_ne_zero`：posRootForm_posForm_pos_
of_ne_zero {x : P.rootSpan S} (hx : x != 0) : 0 < (P.posRootForm S).posForm x x
-/
lemma posRootForm_posForm_anisotropic :
    (P.posRootForm S).posForm.toQuadraticMap.Anisotropic :=
  fun _ hx ↦ Classical.byContradiction fun h ↦
    (ne_of_lt (posRootForm_posForm_pos_of_ne_zero P S h)).symm hx
/-
**RootPairing.posRootForm_posForm_nondegenerate** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing`。
形式化陈述：posRootForm_posForm_nondegenerate : (P.posRootForm S).posForm.Nondegenerat
e
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `RootPairing.posRootForm_posForm_pos_of_ne_zero`：posRootForm_posForm_pos_
of_ne_zero {x : P.rootSpan S} (hx : x != 0) : 0 < (P.posRootForm S).posForm x x
-/
lemma posRootForm_posForm_nondegenerate :
    (P.posRootForm S).posForm.Nondegenerate := by
  constructor <;>
  · intro x
    contrapose!
    exact fun hx ↦ ⟨x, (posRootForm_posForm_pos_of_ne_zero P S hx).ne'⟩

end LinearOrderedCommRingAlg

end CommRing

section IsDomain

variable [CommRing R] [IsDomain R] [Module R M] [Module R N] (P : RootPairing ι R M N)
  [P.IsAnisotropic]

@[simp]
/-
**RootPairing.finrank_rootSpan_map_polarization_eq_finrank_corootSpan** 是 Mathli
b 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：finrank_rootSpan_map_polarization_eq_finrank_corootSpan : finrank R ((P.ro
otSpan R).map P.Polarization) = finrank R (P.corootSpan R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `RootPairing.instIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_
4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _roo
t_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.finrank_range_polarization_eq_finrank_span_coroot`：finrank_r
ange_polarization_eq_finrank_span_coroot [P.IsAnisotropic] : finrank S (LinearMa
p.range (P.PolarizationIn S)) = finrank S (P.coroot…
· 使用定理 `instFaithfulSMul`：∀ (R : Type u_4) [inst : MulOneClass R], FaithfulSMul 
R R
· 使用引理 `RootPairing.range_polarizationIn`：range_polarizationIn : Submodule.map P
.Polarization (P.rootSpan R) = LinearMap.range (P.PolarizationIn R)
-/
lemma finrank_rootSpan_map_polarization_eq_finrank_corootSpan :
    finrank R ((P.rootSpan R).map P.Polarization) = finrank R (P.corootSpan R) := by
  rw [← P.finrank_range_polarization_eq_finrank_span_coroot R, range_polarizationIn]

/-- An auxiliary lemma en route to `RootPairing.finrank_corootSpan_eq'`. -/
/-
**RootPairing.finrank_corootSpan_le'** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary lemma en route to `RootPairing.finrank_corootSpan_eq'`.
-/
private lemma finrank_corootSpan_le' :
    finrank R (P.corootSpan R) ≤ finrank R (P.rootSpan R) := by
  rw [← finrank_rootSpan_map_polarization_eq_finrank_corootSpan]
  exact Submodule.finrank_map_le P.Polarization (P.rootSpan R)

/-- Equality of `finrank`s when the base is a domain. -/
/-
**RootPairing.finrank_corootSpan_eq'** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：finrank_corootSpan_eq' : finrank R (P.corootSpan R) = finrank R (P.rootSpa
n R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `_private.Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate.0.RootPai
ring.finrank_corootSpan_le'`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N :
 Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGroup
 N] [inst…
· 使用定理 `RootPairing.instIsAnisotropicFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_3} {N : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup M]   [inst_2 
: AddCommGroup N] [inst…

--- 原说明 ---
Equality of `finrank`s when the base is a domain.
-/
lemma finrank_corootSpan_eq' :
    finrank R (P.corootSpan R) = finrank R (P.rootSpan R) :=
  le_antisymm P.finrank_corootSpan_le' P.flip.finrank_corootSpan_le'
/-
**RootPairing.disjoint_rootSpan_ker_rootForm** 是 Mathlib 中的一个引理，位于命名空间 `RootPair
ing`。
形式化陈述：disjoint_rootSpan_ker_rootForm : Disjoint (P.rootSpan R) (LinearMap.ker P.
RootForm)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.ker_polarization_eq_ker_rootForm`：ker_polarization_eq_ker_ro
otForm : LinearMap.ker P.Polarization = LinearMap.ker P.RootForm
· 使用引理 `Submodule.disjoint_ker_of_finrank_le`：Submodule.disjoint_ker_of_finrank_
le [IsDomain R] [IsTorsionFree R M] {N : Type*} [AddCommGroup N] [Module R N] {L
 : Submodule R M} [Module.…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `RootPairing.instFiniteSubtypeMemSubmoduleRootSpanOfFinite`：∀ {ι : Type u
_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : A
ddCommGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `RootPairing.finrank_rootSpan_map_polarization_eq_finrank_corootSpan`：fin
rank_rootSpan_map_polarization_eq_finrank_corootSpan : finrank R ((P.rootSpan R)
.map P.Polarization) = finrank R (P.corootSpan R)
· 使用引理 `RootPairing.finrank_corootSpan_eq'`：finrank_corootSpan_eq' : finrank R (
P.corootSpan R) = finrank R (P.rootSpan R)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma disjoint_rootSpan_ker_rootForm :
    Disjoint (P.rootSpan R) (LinearMap.ker P.RootForm) := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  rw [← P.ker_polarization_eq_ker_rootForm]
  refine Submodule.disjoint_ker_of_finrank_le (L := P.rootSpan R) P.Polarization ?_
  rw [P.finrank_rootSpan_map_polarization_eq_finrank_corootSpan, P.finrank_corootSpan_eq']
/-
**RootPairing.disjoint_corootSpan_ker_corootForm** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing`。
形式化陈述：disjoint_corootSpan_ker_corootForm : Disjoint (P.corootSpan R) (LinearMap.
ker P.CorootForm)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.disjoint_rootSpan_ker_rootForm`：disjoint_rootSpan_ker_rootFo
rm : Disjoint (P.rootSpan R) (LinearMap.ker P.RootForm)
· 使用定理 `RootPairing.instIsAnisotropicFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_3} {N : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup M]   [inst_2 
: AddCommGroup N] [inst…
-/
lemma disjoint_corootSpan_ker_corootForm :
    Disjoint (P.corootSpan R) (LinearMap.ker P.CorootForm) :=
  P.flip.disjoint_rootSpan_ker_rootForm
/-
**RootPairing.rootForm_nondegenerate** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：rootForm_nondegenerate [P.IsRootSystem] : P.RootForm.Nondegenerate
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.IsRefl.nondegenerate_iff_separatingLeft`：∀ {R : Type u_1} {M :
 Type u_5} {M₁ : Type u_6} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] [inst_3 : AddCo…
· 使用定理 `LinearMap.IsSymm.isRefl`：isRefl (H : B.IsSymm) : B.IsRefl
· 使用引理 `RootPairing.rootForm_symmetric`：rootForm_symmetric : LinearMap.IsSymm P.
RootForm
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.IsRootSystem.span_root_eq_top`：∀ {ι : Type u_1} {R : Type u_
2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}  
 {inst_2 : _root_.Module R M} {…
· 使用引理 `RootPairing.disjoint_rootSpan_ker_rootForm`：disjoint_rootSpan_ker_rootFo
rm : Disjoint (P.rootSpan R) (LinearMap.ker P.RootForm)
-/
lemma rootForm_nondegenerate [P.IsRootSystem] :
    P.RootForm.Nondegenerate := by
  simpa [(rootForm_symmetric P).isRefl.nondegenerate_iff_separatingLeft,
    LinearMap.separatingLeft_iff_ker_eq_bot] using P.disjoint_rootSpan_ker_rootForm

end IsDomain

section Field

variable [Field R] [Module R M] [Module R N] (P : RootPairing ι R M N) [P.IsAnisotropic]

/-
**RootPairing.isCompl_rootSpan_ker_rootForm** 是 Mathlib 中的一个引理，位于命名空间 `RootPairi
ng`。
形式化陈述：isCompl_rootSpan_ker_rootForm : IsCompl (P.rootSpan R) (LinearMap.ker P.Ro
otForm)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.isCompl_iff_disjoint`：isCompl_iff_disjoint [FiniteDimensional 
K V] (s t : Submodule K V) (hdim : finrank K V <= finrank K s + finrank K t) : I
sCompl s t ↔ Disjoin…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `IsSemisimpleModule.instIsNoetherianOfFinite`：∀ {R : Type u_2} [inst : Ri
ng R] {M : Type u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [I
sSemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `Module.instFiniteDimensionalOfIsReflexive`：∀ (K : Type u_4) (V : Type u_
5) [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [Mo
dule.IsReflexive K V], FiniteDi…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.finrank_corootSpan_eq'`：finrank_corootSpan_eq' : finrank R (
P.corootSpan R) = finrank R (P.rootSpan R)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Subspace.finrank_add_finrank_dualAnnihilator_eq`：finrank_add_finrank_dua
lAnnihilator_eq (W : Subspace K V) : finrank K W + finrank K W.dualAnnihilator =
 finrank K V
· 使用定理 `Subspace.dual_finrank_eq`：dual_finrank_eq : finrank K (Module.Dual K V) 
= finrank K V
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `LinearEquiv.finrank_map_eq`：finrank_map_eq (f : M ≃ₗ[R] N) (p : Submodul
e R M) : finrank R (p.map (f : M ->ₗ[R] N)) = finrank R p
· 使用定理 `Submodule.finrank_mono`：Submodule.finrank_mono {s t : Submodule R M} [Mo
dule.Finite R t] (hst : s <= t) : finrank R s <= finrank R t
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
（共 32 条，此处仅展示前 30 条）
-/
lemma isCompl_rootSpan_ker_rootForm :
    IsCompl (P.rootSpan R) (LinearMap.ker P.RootForm) := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).mpr P.disjoint_rootSpan_ker_rootForm
  have aux : finrank R M =
      finrank R (P.rootSpan R) + finrank R (P.corootSpan R).dualAnnihilator := by
    rw [P.toPerfPair.finrank_eq, ← P.finrank_corootSpan_eq',
      Subspace.finrank_add_finrank_dualAnnihilator_eq (P.corootSpan R), Subspace.dual_finrank_eq]
  rw [aux, add_le_add_iff_left]
  convert! Submodule.finrank_mono P.corootSpan_dualAnnihilator_le_ker_rootForm
  exact (LinearEquiv.finrank_map_eq _ _).symm
/-
**RootPairing.isCompl_corootSpan_ker_corootForm** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing`。
形式化陈述：isCompl_corootSpan_ker_corootForm : IsCompl (P.corootSpan R) (LinearMap.ke
r P.CorootForm)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.isCompl_rootSpan_ker_rootForm`：isCompl_rootSpan_ker_rootForm
 : IsCompl (P.rootSpan R) (LinearMap.ker P.RootForm)
· 使用定理 `RootPairing.instIsAnisotropicFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_3} {N : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup M]   [inst_2 
: AddCommGroup N] [inst…
-/
lemma isCompl_corootSpan_ker_corootForm :
    IsCompl (P.corootSpan R) (LinearMap.ker P.CorootForm) :=
  P.flip.isCompl_rootSpan_ker_rootForm
/-
**RootPairing.ker_rootForm_eq_dualAnnihilator** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring`。
形式化陈述：ker_rootForm_eq_dualAnnihilator : P.RootForm.ker = (P.corootSpan R).dualAn
nihilator.map (P.toPerfPair.symm : Dual R N ->ₗ[R] M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Subspace.finrank_add_finrank_dualAnnihilator_eq`：finrank_add_finrank_dua
lAnnihilator_eq (W : Subspace K V) : finrank K W + finrank K W.dualAnnihilator =
 finrank K V
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `IsSemisimpleModule.instIsNoetherianOfFinite`：∀ {R : Type u_2} [inst : Ri
ng R] {M : Type u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [I
sSemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `Module.instFiniteDimensionalOfIsReflexive`：∀ (K : Type u_4) (V : Type u_
5) [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [Mo
dule.IsReflexive K V], FiniteDi…
· 使用定理 `Submodule.finrank_add_eq_of_isCompl`：finrank_add_eq_of_isCompl [FiniteDi
mensional K V] {U W : Submodule K V} (h : IsCompl U W) : finrank K U + finrank K
 W = finrank K V
· 使用引理 `RootPairing.isCompl_rootSpan_ker_rootForm`：isCompl_rootSpan_ker_rootForm
 : IsCompl (P.rootSpan R) (LinearMap.ker P.RootForm)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subspace.dual_finrank_eq`：dual_finrank_eq : finrank K (Module.Dual K V) 
= finrank K V
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.finrank_corootSpan_eq'`：finrank_corootSpan_eq' : finrank R (
P.corootSpan R) = finrank R (P.rootSpan R)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Submodule.eq_of_le_of_finrank_eq`：eq_of_le_of_finrank_eq {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₁ = finrank 
K S₂) : S₁ = S₂
· 使用定理 `RootPairing.corootSpan_dualAnnihilator_le_ker_rootForm`：corootSpan_dualA
nnihilator_le_ker_rootForm : (P.corootSpan R).dualAnnihilator.map (P.toPerfPair.
symm : Dual R N ->ₗ[R] M) <= P.RootForm.ker
· 使用定理 `LinearEquiv.finrank_map_eq`：finrank_map_eq (f : M ≃ₗ[R] N) (p : Submodul
e R M) : finrank R (p.map (f : M ->ₗ[R] N)) = finrank R p
-/
lemma ker_rootForm_eq_dualAnnihilator :
    P.RootForm.ker =
      (P.corootSpan R).dualAnnihilator.map (P.toPerfPair.symm : Dual R N →ₗ[R] M) := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  suffices finrank R (LinearMap.ker P.RootForm) = finrank R (P.corootSpan R).dualAnnihilator by
    refine (Submodule.eq_of_le_of_finrank_eq P.corootSpan_dualAnnihilator_le_ker_rootForm ?_).symm
    rw [this]
    apply LinearEquiv.finrank_map_eq
  have aux0 := Subspace.finrank_add_finrank_dualAnnihilator_eq (P.corootSpan R)
  have aux1 := Submodule.finrank_add_eq_of_isCompl P.isCompl_rootSpan_ker_rootForm
  rw [← P.finrank_corootSpan_eq', P.toPerfPair.finrank_eq, Subspace.dual_finrank_eq] at aux1
  lia
/-
**RootPairing.ker_corootForm_eq_dualAnnihilator** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing`。
形式化陈述：ker_corootForm_eq_dualAnnihilator : P.CorootForm.ker = (P.rootSpan R).dual
Annihilator.map (P.flip.toPerfPair.symm : Dual R M ->ₗ[R] N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.ker_rootForm_eq_dualAnnihilator`：ker_rootForm_eq_dualAnnihil
ator : P.RootForm.ker = (P.corootSpan R).dualAnnihilator.map (P.toPerfPair.symm 
: Dual R N ->ₗ[R] M)
· 使用定理 `RootPairing.instIsAnisotropicFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_3} {N : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup M]   [inst_2 
: AddCommGroup N] [inst…
-/
lemma ker_corootForm_eq_dualAnnihilator :
    P.CorootForm.ker =
      (P.rootSpan R).dualAnnihilator.map (P.flip.toPerfPair.symm : Dual R M →ₗ[R] N) :=
  P.flip.ker_rootForm_eq_dualAnnihilator
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.IsBalanced where
    isPerfectCompl :=
  { isCompl_left := by
      simpa only [ker_rootForm_eq_dualAnnihilator] using! P.isCompl_rootSpan_ker_rootForm
    isCompl_right := by
      simpa only [ker_corootForm_eq_dualAnnihilator] using! P.isCompl_corootSpan_ker_corootForm }

/-- See also `RootPairing.rootForm_restrict_nondegenerate_of_ordered`.

Note that this applies to crystallographic root systems in characteristic zero via
`RootPairing.instIsAnisotropicOfIsCrystallographic`. -/
/-
**RootPairing.rootForm_restrict_nondegenerate_of_isAnisotropic** 是 Mathlib 中的一个引
理，位于命名空间 `RootPairing`。
形式化陈述：rootForm_restrict_nondegenerate_of_isAnisotropic : LinearMap.Nondegenerate
 (P.RootForm.restrict (P.rootSpan R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymm.nondegenerate_restrict_of_isCompl_ker`：∀ {R : Type u_1}
 {M : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.M
odule R M]   {B : M →ₗ[R] M →ₗ[R] R}, B.IsSy…
· 使用引理 `RootPairing.rootForm_symmetric`：rootForm_symmetric : LinearMap.IsSymm P.
RootForm
· 使用引理 `RootPairing.isCompl_rootSpan_ker_rootForm`：isCompl_rootSpan_ker_rootForm
 : IsCompl (P.rootSpan R) (LinearMap.ker P.RootForm)

--- 原说明 ---
See also `RootPairing.rootForm_restrict_nondegenerate_of_ordered`.

Note that this applies to crystallographic root systems in characteristic zero v
ia
`RootPairing.instIsAnisotropicOfIsCrystallographic`.
-/
lemma rootForm_restrict_nondegenerate_of_isAnisotropic :
    LinearMap.Nondegenerate (P.RootForm.restrict (P.rootSpan R)) :=
  P.rootForm_symmetric.nondegenerate_restrict_of_isCompl_ker P.isCompl_rootSpan_ker_rootForm

@[simp]
/-
**RootPairing.orthogonal_rootSpan_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：orthogonal_rootSpan_eq : P.RootForm.orthogonal (P.rootSpan R) = LinearMap.
ker P.RootForm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.BilinForm.orthogonal_top_eq_ker`：orthogonal_top_eq_ker (hB : B
.IsRefl) : B.orthogonal ⊤ = LinearMap.ker B
· 使用定理 `LinearMap.IsSymm.isRefl`：isRefl (H : B.IsSymm) : B.IsRefl
· 使用引理 `RootPairing.rootForm_symmetric`：rootForm_symmetric : LinearMap.IsSymm P.
RootForm
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用引理 `RootPairing.isCompl_rootSpan_ker_rootForm`：isCompl_rootSpan_ker_rootForm
 : IsCompl (P.rootSpan R) (LinearMap.ker P.RootForm)
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma orthogonal_rootSpan_eq :
    P.RootForm.orthogonal (P.rootSpan R) = LinearMap.ker P.RootForm := by
  rw [← LinearMap.BilinForm.orthogonal_top_eq_ker P.rootForm_symmetric.isRefl]
  refine le_antisymm ?_ (by intro; simp_all)
  rintro x hx y -
  simp only [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
  obtain ⟨u, hu, v, hv, rfl⟩ : ∃ᵉ (u ∈ P.rootSpan R) (v ∈ LinearMap.ker P.RootForm), u + v = y := by
    rw [← Submodule.mem_sup, P.isCompl_rootSpan_ker_rootForm.sup_eq_top]; exact Submodule.mem_top
  simp only [LinearMap.mem_ker] at hv
  simp [hx _ hu, hv]

@[simp]
/-
**RootPairing.orthogonal_corootSpan_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：orthogonal_corootSpan_eq : P.CorootForm.orthogonal (P.corootSpan R) = Line
arMap.ker P.CorootForm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.orthogonal_rootSpan_eq`：orthogonal_rootSpan_eq : P.RootForm.
orthogonal (P.rootSpan R) = LinearMap.ker P.RootForm
· 使用定理 `RootPairing.instIsAnisotropicFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_3} {N : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup M]   [inst_2 
: AddCommGroup N] [inst…
-/
lemma orthogonal_corootSpan_eq :
    P.CorootForm.orthogonal (P.corootSpan R) = LinearMap.ker P.CorootForm :=
  P.flip.orthogonal_rootSpan_eq
/-
**RootPairing.rootSpan_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：rootSpan_eq_top_iff : P.rootSpan R = ⊤ ↔ P.corootSpan R = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `Submodule.eq_top_of_finrank_eq`：∀ {K : Type u} {V : Type v} [inst : Divi
sionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [FiniteDime
nsional K V] {S : Su…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `IsSemisimpleModule.instIsNoetherianOfFinite`：∀ {R : Type u_2} [inst : Ri
ng R] {M : Type u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [I
sSemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `Module.instFiniteDimensionalOfIsReflexive`：∀ (K : Type u_4) (V : Type u_
5) [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [Mo
dule.IsReflexive K V], FiniteDi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.finrank_corootSpan_eq'`：finrank_corootSpan_eq' : finrank R (
P.corootSpan R) = finrank R (P.rootSpan R)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Subspace.dual_finrank_eq`：dual_finrank_eq : finrank K (Module.Dual K V) 
= finrank K V
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma rootSpan_eq_top_iff :
    P.rootSpan R = ⊤ ↔ P.corootSpan R = ⊤ := by
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> apply Submodule.eq_top_of_finrank_eq
  · rw [P.finrank_corootSpan_eq', h, finrank_top, P.toPerfPair.finrank_eq, Subspace.dual_finrank_eq]
  · rw [← P.finrank_corootSpan_eq', h, finrank_top, P.toPerfPair.finrank_eq,
      Subspace.dual_finrank_eq]

section IsRootSystem

variable [P.IsRootSystem]

/-- The polarization map from weight space to coweight space as an equivalence. -/
/-
**RootPairing.PolarizationEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：PolarizationEquiv : M ≃ₗ[R] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polarization map from weight space to coweight space as an equivalence.
-/
def PolarizationEquiv : M ≃ₗ[R] N :=
  have : IsReflexive R M := Module.IsReflexive.of_isPerfPair P.toLinearMap
  (P.toInvariantForm.form.toDual P.rootForm_nondegenerate).trans P.flip.toPerfPair.symm

@[simp]
/-
**RootPairing.polarizationEquiv_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `RootPairi
ng`。
形式化陈述：polarizationEquiv_toLinearMap : P.PolarizationEquiv.toLinearMap = P.Polari
zation
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RootPairing.toInvariantForm_form`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup M]   [inst_2 :
 AddCommGroup N] [inst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.flip_comp_polarization_eq_rootForm`：flip_comp_polarization_e
q_rootForm : P.flip.toLinearMap ∘ₗ P.Polarization = P.RootForm
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `RootPairing.flip_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M : Type 
u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _r
oot_.Module R M] […
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `LinearMap.linearEquivOfInjective.congr_simp`：∀ {K : Type u} {V : Type v}
 [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] 
  {V₂ : Type v'} [inst_3 : AddCom…
· 使用定理 `LinearMap.toPerfPair.congr_simp`：∀ {R : Type u_1} {M : Type u_3} {N : Ty
pe u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R] 
  [inst_3 : _root_.Mo…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.Polarization_apply`：Polarization_apply (x : M) : P.Polarizat
ion x = ∑ i, P.coroot' i x • P.coroot i
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma polarizationEquiv_toLinearMap :
    P.PolarizationEquiv.toLinearMap = P.Polarization := by
  simp only [PolarizationEquiv, LinearMap.BilinForm.toDual, RootPairing.toInvariantForm_form,
    ← P.flip_comp_polarization_eq_rootForm, RootPairing.flip_toLinearMap]
  ext m
  let e := P.flip.toPerfPair
  change e.symm (e _) = _
  simp

-- Not `simp` to avoid losing the information that we're applying an `Equiv`.
/-
**RootPairing.polarizationEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：polarizationEquiv_apply (m : M) : P.PolarizationEquiv m = P.Polarization m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.polarizationEquiv_toLinearMap`：polarizationEquiv_toLinearMap
 : P.PolarizationEquiv.toLinearMap = P.Polarization
-/
lemma polarizationEquiv_apply (m : M) :
    P.PolarizationEquiv m = P.Polarization m :=
  congr($P.polarizationEquiv_toLinearMap m)
/-
**RootPairing.coroot_eq_polarizationEquiv_apply_root** 是 Mathlib 中的一个引理，位于命名空间 `
RootPairing`。
形式化陈述：coroot_eq_polarizationEquiv_apply_root (i : ι) : P.coroot i = (2 / P.RootF
orm (P.root i) (P.root i)) • P.PolarizationEquiv (P.root i)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsAnisotropic.rootForm_root_ne_zero`：∀ {ι : Type u_1} {R : T
ype u_2} {M : Type u_3} {N : Type u_4} {inst : Fintype ι} {inst_1 : AddCommGroup
 M}   {inst_2 : AddCommGroup N} {inst…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.polarizationEquiv_apply`：polarizationEquiv_apply (m : M) : P
.PolarizationEquiv m = P.Polarization m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `RootPairing.rootForm_self_smul_coroot`：rootForm_self_smul_coroot (i : ι)
 : (P.RootForm (P.root i) (P.root i)) • P.coroot i = 2 • P.Polarization (P.root 
i)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
-/
lemma coroot_eq_polarizationEquiv_apply_root (i : ι) :
    P.coroot i = (2 / P.RootForm (P.root i) (P.root i)) • P.PolarizationEquiv (P.root i) := by
  have h₀ := IsAnisotropic.rootForm_root_ne_zero (P := P) i
  rw [polarizationEquiv_apply, ← (smul_right_injective N h₀).eq_iff, P.rootForm_self_smul_coroot i,
    smul_smul, mul_div_cancel₀ _ h₀]
  norm_cast
/-
**RootPairing.polarizationEquiv_symm_apply_coroot** 是 Mathlib 中的一个引理，位于命名空间 `Roo
tPairing`。
形式化陈述：polarizationEquiv_symm_apply_coroot {i : ι} : P.PolarizationEquiv.symm (P.
coroot i) = (2 / P.RootForm (P.root i) (P.root i)) • P.root i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.coroot_eq_polarizationEquiv_apply_root`：coroot_eq_polarizati
onEquiv_apply_root (i : ι) : P.coroot i = (2 / P.RootForm (P.root i) (P.root i))
 • P.PolarizationEquiv (P.root i)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma polarizationEquiv_symm_apply_coroot {i : ι} :
    P.PolarizationEquiv.symm (P.coroot i) = (2 / P.RootForm (P.root i) (P.root i)) • P.root i := by
  simp [coroot_eq_polarizationEquiv_apply_root]

variable [NeZero (2 : R)]
/-
**RootPairing.linearIndepOn_coroot_iff_aux** 是 Mathlib 中的一个引理，位于命名空间 `RootPairin
g`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma linearIndepOn_coroot_iff_aux {s : Set ι} (h : LinearIndepOn R P.root s) :
    LinearIndepOn R P.coroot s := by
  obtain ⟨f, hf⟩ : ∃ f : s → Rˣ, ∀ i : s, P.coroot i = f i • P.PolarizationEquiv (P.root i) :=
    ⟨fun i ↦ Units.mk0 (2 / P.RootForm (P.root i) (P.root i))
      (by simp [two_ne_zero, IsAnisotropic.rootForm_root_ne_zero]),
     fun i ↦ by simp [coroot_eq_polarizationEquiv_apply_root]⟩
  have : s.domRestrict P.coroot = P.PolarizationEquiv.toLinearMap ∘ (f • s.domRestrict P.root) := by
    ext; simp [hf, polarizationEquiv_apply]
  rw [← linearIndependent_restrict_iff, this,
    LinearMap.linearIndependent_iff_of_injOn _ P.PolarizationEquiv.injective.injOn]
  simpa
/-
**RootPairing.linearIndepOn_coroot_iff** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Fint
ype ι] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGroup N] [inst_3 : Field R] 
[inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   (P : RootPairing ι R
 M N) [P.IsAnisotropic] [P.IsRootSystem] [NeZero 2] {s : Set ι},   LinearIndepOn
 R (⇑P.coroot) s ↔ LinearIndepOn R (⇑P.root) s
参数：P : RootPairing ι R M N；⇑P.coroot；⇑P.root。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `_private.Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate.0.RootPai
ring.linearIndepOn_coroot_iff_aux`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3
} {N : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup M]   [inst_2 : AddCom
mGroup N] [inst…
· 使用定理 `RootPairing.instIsAnisotropicFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_3} {N : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup M]   [inst_2 
: AddCommGroup N] [inst…
· 使用定理 `RootPairing.instIsRootSystemFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] […
-/
@[simp] lemma linearIndepOn_coroot_iff {s : Set ι} :
    LinearIndepOn R P.coroot s ↔ LinearIndepOn R P.root s :=
  ⟨P.flip.linearIndepOn_coroot_iff_aux, P.linearIndepOn_coroot_iff_aux⟩

end IsRootSystem

end Field

section LinearOrderedCommRing

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [Module R M] [Module R N] (P : RootPairing ι R M N)

/-
**RootPairing.instIsAnisotropicOfLinearOrderedCommRing** 是 Mathlib 中的一个实例，位于命名空间
 `RootPairing`。
形式化陈述：instIsAnisotropicOfLinearOrderedCommRing : IsAnisotropic P
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.isAnisotropic_of_isValuedIn`：isAnisotropic_of_isValuedIn (S 
: Type*) [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] [Algebra S R] [Fai
thfulSMul S R] [P.IsValuedIn …
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `RootPairing.instIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_
4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _roo
t_.Module R M] […
-/
instance instIsAnisotropicOfLinearOrderedCommRing : IsAnisotropic P :=
  P.isAnisotropic_of_isValuedIn R
/-
**RootPairing.zero_le_rootForm** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：zero_le_rootForm (x : M) : 0 <= P.RootForm x x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSumSq.nonneg`：IsSumSq.nonneg {R : Type*} [Semiring R] [LinearOrder R] 
[IsStrictOrderedRing R] [ExistsAddOfLE R] {s : R} (hs : IsSumSq s) : 0 <= s
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `RootPairing.rootForm_self_sum_of_squares`：rootForm_self_sum_of_squares (
x : M) : IsSumSq (P.RootForm x x)
-/
lemma zero_le_rootForm (x : M) :
    0 ≤ P.RootForm x x :=
  (P.rootForm_self_sum_of_squares x).nonneg

/-- See also `RootPairing.rootForm_restrict_nondegenerate_of_isAnisotropic`. -/
/-
**RootPairing.rootForm_restrict_nondegenerate_of_ordered** 是 Mathlib 中的一个引理，位于命名
空间 `RootPairing`。
形式化陈述：rootForm_restrict_nondegenerate_of_ordered : LinearMap.Nondegenerate (P.Ro
otForm.restrict (P.rootSpan R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.BilinForm.nondegenerate_restrict_iff_disjoint_ker`：nondegenera
te_restrict_iff_disjoint_ker (hs : forall x, 0 <= B x x) (hB : B.IsSymm) {W : Su
bmodule R M} : (B.domRestrict₁₂ W W).Nondegenerat…
· 使用引理 `RootPairing.zero_le_rootForm`：zero_le_rootForm (x : M) : 0 <= P.RootForm
 x x
· 使用引理 `RootPairing.rootForm_symmetric`：rootForm_symmetric : LinearMap.IsSymm P.
RootForm
· 使用引理 `RootPairing.disjoint_rootSpan_ker_rootForm`：disjoint_rootSpan_ker_rootFo
rm : Disjoint (P.rootSpan R) (LinearMap.ker P.RootForm)
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α

--- 原说明 ---
See also `RootPairing.rootForm_restrict_nondegenerate_of_isAnisotropic`.
-/
lemma rootForm_restrict_nondegenerate_of_ordered :
    LinearMap.Nondegenerate (P.RootForm.restrict (P.rootSpan R)) :=
  (P.RootForm.nondegenerate_restrict_iff_disjoint_ker P.zero_le_rootForm
    P.rootForm_symmetric).mpr P.disjoint_rootSpan_ker_rootForm
/-
**RootPairing.rootForm_self_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：rootForm_self_eq_zero_iff {x : M} : P.RootForm x x = 0 ↔ x in LinearMap.ke
r P.RootForm
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.BilinForm.apply_apply_same_eq_zero_iff`：apply_apply_same_eq_ze
ro_iff (hs : forall x, 0 <= B x x) (hB : B.IsSymm) {x : M} : B x x = 0 ↔ x in Li
nearMap.ker B
· 使用引理 `RootPairing.zero_le_rootForm`：zero_le_rootForm (x : M) : 0 <= P.RootForm
 x x
· 使用引理 `RootPairing.rootForm_symmetric`：rootForm_symmetric : LinearMap.IsSymm P.
RootForm
-/
lemma rootForm_self_eq_zero_iff {x : M} :
    P.RootForm x x = 0 ↔ x ∈ LinearMap.ker P.RootForm :=
  P.RootForm.apply_apply_same_eq_zero_iff P.zero_le_rootForm P.rootForm_symmetric
/-
**RootPairing.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero** 是 Mathlib 中的一个引
理，位于命名空间 `RootPairing`。
形式化陈述：eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero {x : M} (hx : x in P.root
Span R) (hx' : P.RootForm x x = 0) : x = 0
参数：hx : x in P.rootSpan R；hx' : P.RootForm x x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RootPairing.rootForm_self_eq_zero_iff`：rootForm_self_eq_zero_iff {x : M}
 : P.RootForm x x = 0 ↔ x in LinearMap.ker P.RootForm
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用引理 `RootPairing.disjoint_rootSpan_ker_rootForm`：disjoint_rootSpan_ker_rootFo
rm : Disjoint (P.rootSpan R) (LinearMap.ker P.RootForm)
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
-/
lemma eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero {x : M}
    (hx : x ∈ P.rootSpan R) (hx' : P.RootForm x x = 0) :
    x = 0 := by
  have : x ∈ P.rootSpan R ⊓ LinearMap.ker P.RootForm := ⟨hx, P.rootForm_self_eq_zero_iff.mp hx'⟩
  simpa [P.disjoint_rootSpan_ker_rootForm.eq_bot] using this
/-
**RootPairing.rootForm_pos_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：rootForm_pos_of_ne_zero {x : M} (hx : x in P.rootSpan R) (h : x != 0) : 0 
< P.RootForm x x
参数：hx : x in P.rootSpan R；h : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用引理 `RootPairing.zero_le_rootForm`：zero_le_rootForm (x : M) : 0 <= P.RootForm
 x x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用引理 `RootPairing.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero`：eq_zero_of
_mem_rootSpan_of_rootForm_self_eq_zero {x : M} (hx : x in P.rootSpan R) (hx' : P
.RootForm x x = 0) : x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma rootForm_pos_of_ne_zero {x : M} (hx : x ∈ P.rootSpan R) (h : x ≠ 0) :
    0 < P.RootForm x x := by
  apply (P.zero_le_rootForm x).lt_of_ne
  contrapose h
  exact P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero hx h.symm
/-
**RootPairing.rootForm_anisotropic** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：rootForm_anisotropic [P.IsRootSystem] : P.RootForm.toQuadraticMap.Anisotro
pic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero`：eq_zero_of
_mem_rootSpan_of_rootForm_self_eq_zero {x : M} (hx : x in P.rootSpan R) (hx' : P
.RootForm x x = 0) : x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.IsRootSystem.span_root_eq_top`：∀ {ι : Type u_1} {R : Type u_
2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}  
 {inst_2 : _root_.Module R M} {…
-/
lemma rootForm_anisotropic [P.IsRootSystem] :
    P.RootForm.toQuadraticMap.Anisotropic :=
  fun x ↦ P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero <| by simp

end LinearOrderedCommRing

end RootPairing

