/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Jacobson.Polynomial

/-!
# Jacobson Rings

The following conditions are equivalent for a ring `R`:
1. Every radical ideal `I` is equal to its Jacobson radical
2. Every radical ideal `I` can be written as an intersection of maximal ideals
3. Every prime ideal `I` is equal to its Jacobson radical

Any ring satisfying any of these equivalent conditions is said to be Jacobson.
Some particular examples of Jacobson rings are also proven.
- `isJacobsonRing_quotient` says that the quotient of a Jacobson ring is Jacobson.
- `isJacobsonRing_localization` says the localization of a Jacobson ring
  to a single element is Jacobson.
- `isJacobsonRing_polynomial_iff_isJacobsonRing` says polynomials over a Jacobson ring
  form a Jacobson ring.

## Main definitions
Let `R` be a commutative ring. Jacobson rings are defined using the first of the above conditions
* `IsJacobsonRing R` is the proposition that `R` is a Jacobson ring. It is a class,
  implemented as the predicate that for any ideal, `I.isRadical` implies `I.jacobson = I`.

## Main statements
* `isJacobsonRing_iff_prime_eq` is the equivalence between conditions 1 and 3 above.
* `isJacobsonRing_iff_sInf_maximal` is the equivalence between conditions 1 and 2 above.
* `isJacobsonRing_of_surjective` says that if `R` is a Jacobson ring and
  `f : R →+* S` is surjective, then `S` is also a Jacobson ring
* `MvPolynomial.isJacobsonRing` says that multi-variate polynomials
  over a Jacobson ring are Jacobson.

## Tags
Jacobson, Jacobson Ring
-/

@[expose] public section

universe u

open Polynomial
open Ideal

section IsJacobsonRing

variable {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R}

/-- A ring is a Jacobson ring if for every radical ideal `I`,
the Jacobson radical of `I` is equal to `I`.
See `isJacobsonRing_iff_prime_eq` and `isJacobsonRing_iff_sInf_maximal`
for equivalent definitions. -/
/-
**IsJacobsonRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_3) → [CommRing R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring is a Jacobson ring if for every radical ideal `I`,
the Jacobson radical of `I` is equal to `I`.
See `isJacobsonRing_iff_prime_eq` and `isJacobsonRing_iff_sInf_maximal`
for equivalent definitions.
-/
class IsJacobsonRing (R : Type*) [CommRing R] : Prop where
  out' : ∀ I : Ideal R, I.IsRadical → I.jacobson = I
/-
**isJacobsonRing_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isJacobsonRing_iff {R} [CommRing R] : IsJacobsonRing R ↔ forall I : Ideal 
R, I.IsRadical -> I.jacobson = I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsJacobsonRing.out'`：∀ {R : Type u_3} {inst : CommRing R} [self : IsJaco
bsonRing R] (I : Ideal R), I.IsRadical → I.jacobson = I
-/
theorem isJacobsonRing_iff {R} [CommRing R] :
    IsJacobsonRing R ↔ ∀ I : Ideal R, I.IsRadical → I.jacobson = I :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
/-
**IsJacobsonRing.out** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsJacobsonRing.out {R} [CommRing R] : IsJacobsonRing R -> forall {I : Idea
l R}, I.IsRadical -> I.jacobson = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isJacobsonRing_iff`：isJacobsonRing_iff {R} [CommRing R] : IsJacobsonRing
 R ↔ forall I : Ideal R, I.IsRadical -> I.jacobson = I
-/
theorem IsJacobsonRing.out {R} [CommRing R] :
    IsJacobsonRing R → ∀ {I : Ideal R}, I.IsRadical → I.jacobson = I :=
  isJacobsonRing_iff.1

/-- A ring is a Jacobson ring if and only if for all prime ideals `P`,
the Jacobson radical of `P` is equal to `P`. -/
/-
**isJacobsonRing_iff_prime_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isJacobsonRing_iff_prime_eq : IsJacobsonRing R ↔ forall P : Ideal R, IsPri
me P -> P.jacobson = P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isJacobsonRing_iff`：isJacobsonRing_iff {R} [CommRing R] : IsJacobsonRing
 R ↔ forall I : Ideal R, I.IsRadical -> I.jacobson = I
· 使用定理 `Ideal.IsPrime.isRadical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ide
al R}, I.IsPrime → I.IsRadical
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsRadical.radical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ide
al R}, I.IsRadical → I.radical = I
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Ideal.jacobson.eq_1`：∀ {R : Type u} [inst : Ring R] (I : Ideal R), I.jac
obson = sInf {J | I ≤ J ∧ J.IsMaximal}
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
A ring is a Jacobson ring if and only if for all prime ideals `P`,
the Jacobson radical of `P` is equal to `P`.
-/
theorem isJacobsonRing_iff_prime_eq :
    IsJacobsonRing R ↔ ∀ P : Ideal R, IsPrime P → P.jacobson = P := by
  refine isJacobsonRing_iff.trans ⟨fun h I hI => h I hI.isRadical, ?_⟩
  refine fun h I hI ↦ le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ mem_sInf.mpr fun _ hJ ↦ hJ.left hx)
  rw [← hI.radical, radical_eq_sInf I, mem_sInf]
  intro P hP
  rw [Set.mem_ofPred_eq] at hP
  rw [jacobson, mem_sInf] at hx
  rw [← h P hP.right, jacobson, mem_sInf]
  exact fun J hJ => hx ⟨le_trans hP.left hJ.left, hJ.right⟩

/-- A ring `R` is Jacobson if and only if for every prime ideal `I`,
`I` can be written as the infimum of some collection of maximal ideals.
Allowing ⊤ in the set `M` of maximal ideals is equivalent, but makes some proofs cleaner. -/
/-
**isJacobsonRing_iff_sInf_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isJacobsonRing_iff_sInf_maximal : IsJacobsonRing R ↔ forall {I : Ideal R},
 I.IsPrime -> exists M : Set (Ideal R), (forall J in M, IsMaximal J ∨ J = ⊤) ∧ I
 = sInf M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.eq_jacobson_iff_sInf_maximal`：eq_jacobson_iff_sInf_maximal : I.jac
obson = I ↔ exists M : Set (Ideal R), (forall J in M, IsMaximal J ∨ J = ⊤) ∧ I =
 sInf M
· 使用定理 `IsJacobsonRing.out`：IsJacobsonRing.out {R} [CommRing R] : IsJacobsonRing
 R -> forall {I : Ideal R}, I.IsRadical -> I.jacobson = I
· 使用定理 `Ideal.IsPrime.isRadical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ide
al R}, I.IsPrime → I.IsRadical
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isJacobsonRing_iff_prime_eq`：isJacobsonRing_iff_prime_eq : IsJacobsonRin
g R ↔ forall P : Ideal R, IsPrime P -> P.jacobson = P

--- 原说明 ---
A ring `R` is Jacobson if and only if for every prime ideal `I`,
`I` can be written as the infimum of some collection of maximal ideals.
Allowing ⊤ in the set `M` of maximal ideals is equivalent, but makes some proofs
 cleaner.
-/
theorem isJacobsonRing_iff_sInf_maximal : IsJacobsonRing R ↔ ∀ {I : Ideal R}, I.IsPrime →
    ∃ M : Set (Ideal R), (∀ J ∈ M, IsMaximal J ∨ J = ⊤) ∧ I = sInf M :=
  ⟨fun H _I h => eq_jacobson_iff_sInf_maximal.1 (H.out h.isRadical), fun H =>
    isJacobsonRing_iff_prime_eq.2 fun _P hP => eq_jacobson_iff_sInf_maximal.2 (H hP)⟩

/-- A variant of `isJacobsonRing_iff_sInf_maximal` with a different spelling of "maximal or `⊤`". -/
/-
**isJacobsonRing_iff_sInf_maximal'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isJacobsonRing_iff_sInf_maximal' : IsJacobsonRing R ↔ forall {I : Ideal R}
, I.IsPrime -> exists M : Set (Ideal R), (forall J in M, forall (K : Ideal R), J
 < K -> K = ⊤) ∧ I = sInf M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.eq_jacobson_iff_sInf_maximal'`：eq_jacobson_iff_sInf_maximal' : I.j
acobson = I ↔ exists M : Set (Ideal R), (forall J in M, forall (K : Ideal R), J 
< K -> K = ⊤) ∧ I = sInf …
· 使用定理 `IsJacobsonRing.out`：IsJacobsonRing.out {R} [CommRing R] : IsJacobsonRing
 R -> forall {I : Ideal R}, I.IsRadical -> I.jacobson = I
· 使用定理 `Ideal.IsPrime.isRadical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ide
al R}, I.IsPrime → I.IsRadical
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isJacobsonRing_iff_prime_eq`：isJacobsonRing_iff_prime_eq : IsJacobsonRin
g R ↔ forall P : Ideal R, IsPrime P -> P.jacobson = P

--- 原说明 ---
A variant of `isJacobsonRing_iff_sInf_maximal` with a different spelling of "max
imal or `⊤`".
-/
theorem isJacobsonRing_iff_sInf_maximal' : IsJacobsonRing R ↔ ∀ {I : Ideal R}, I.IsPrime →
    ∃ M : Set (Ideal R), (∀ J ∈ M, ∀ (K : Ideal R), J < K → K = ⊤) ∧ I = sInf M :=
  ⟨fun H _I h => eq_jacobson_iff_sInf_maximal'.1 (H.out h.isRadical), fun H =>
    isJacobsonRing_iff_prime_eq.2 fun _P hP => eq_jacobson_iff_sInf_maximal'.2 (H hP)⟩
/-
**Ideal.radical_eq_jacobson** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.radical_eq_jacobson [H : IsJacobsonRing R] (I : Ideal R) : I.radical
 = I.jacobson
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.IsPrime.radical_le_iff`：∀ {R : Type u} [inst : CommSemiring R] {I 
J : Ideal R}, J.IsPrime → (I.radical ≤ J ↔ I ≤ J)
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Ideal.jacobson_mono`：jacobson_mono {I J : Ideal R} : I <= J -> I.jacobso
n <= J.jacobson
· 使用定理 `Ideal.le_radical`：le_radical : I <= radical I
· 使用定理 `IsJacobsonRing.out`：IsJacobsonRing.out {R} [CommRing R] : IsJacobsonRing
 R -> forall {I : Ideal R}, I.IsRadical -> I.jacobson = I
· 使用定理 `Ideal.radical_isRadical`：radical_isRadical : (radical I).IsRadical
-/
theorem Ideal.radical_eq_jacobson [H : IsJacobsonRing R] (I : Ideal R) : I.radical = I.jacobson :=
  le_antisymm (le_sInf fun _J ⟨hJ, hJ_max⟩ => (IsPrime.radical_le_iff hJ_max.isPrime).mpr hJ)
    (H.out (radical_isRadical I) ▸ jacobson_mono le_radical)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [IsArtinianRing R] : IsJacobsonRing R :=
  isJacobsonRing_iff_prime_eq.mpr fun _ _ ↦ jacobson_eq_self_of_isMaximal
/-
**isJacobsonRing_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isJacobsonRing_of_surjective [H : IsJacobsonRing R] : (exists f : R ->+* S
, Function.Surjective ↑f) -> IsJacobsonRing S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isJacobsonRing_iff_sInf_maximal`：isJacobsonRing_iff_sInf_maximal : IsJac
obsonRing R ↔ forall {I : Ideal R}, I.IsPrime -> exists M : Set (Ideal R), (fora
ll J in M, IsMaximal …
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Ideal.map_eq_top_or_isMaximal_of_surjective`：map_eq_top_or_isMaximal_of_
surjective (hf : Function.Surjective f) {I : Ideal R} (H : IsMaximal I) : map f 
I = ⊤ ∨ IsMaximal (map f I)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_comap_of_surjective`：map_comap_of_surjective (I : Ideal S) : m
ap f (comap f I) = I
· 使用定理 `IsJacobsonRing.out'`：∀ {R : Type u_3} {inst : CommRing R} [self : IsJaco
bsonRing R] (I : Ideal R), I.IsRadical → I.jacobson = I
· 使用定理 `Ideal.IsRadical.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst 
: CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : Rin
gHomClass F…
· 使用定理 `Ideal.IsPrime.isRadical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ide
al R}, I.IsPrime → I.IsRadical
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.map_sInf`：map_sInf {A : Set (Ideal R)} {f : F} (hf : Function.Surj
ective f) : (forall J in A, RingHom.ker f <= J) -> map f (sInf A) = sInf (map f 
'' A…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Ideal.ker_le_comap`：ker_le_comap {K : Ideal S} (f : F) : RingHom.ker f <
= comap f K
-/
theorem isJacobsonRing_of_surjective [H : IsJacobsonRing R] :
    (∃ f : R →+* S, Function.Surjective ↑f) → IsJacobsonRing S := by
  rintro ⟨f, hf⟩
  rw [isJacobsonRing_iff_sInf_maximal]
  intro p hp
  use map f '' { J : Ideal R | comap f p ≤ J ∧ J.IsMaximal }
  use fun j ⟨J, hJ, hmap⟩ => hmap ▸ (map_eq_top_or_isMaximal_of_surjective f hf hJ.right).symm
  have : p = map f (comap f p).jacobson :=
    (IsJacobsonRing.out' _ <| hp.isRadical.comap f).symm ▸ (map_comap_of_surjective f hf p).symm
  exact this.trans (map_sInf hf fun J ⟨hJ, _⟩ => le_trans (Ideal.ker_le_comap f) hJ)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isJacobsonRing_quotient [IsJacobsonRing R] : IsJacobsonRing (R ⧸ I) :=
  isJacobsonRing_of_surjective ⟨Ideal.Quotient.mk I, by
    rintro ⟨x⟩
    use x
    rfl⟩
/-
**isJacobsonRing_iso** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isJacobsonRing_iso (e : R ≃+* S) : IsJacobsonRing R ↔ IsJacobsonRing S whe
re mp _
参数：e : R ≃+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isJacobsonRing_of_surjective`：isJacobsonRing_of_surjective [H : IsJacobs
onRing R] : (exists f : R ->+* S, Function.Surjective ↑f) -> IsJacobsonRing S
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
-/
theorem isJacobsonRing_iso (e : R ≃+* S) : IsJacobsonRing R ↔ IsJacobsonRing S where
  mp _ := isJacobsonRing_of_surjective ⟨(e : R →+* S), e.surjective⟩
  mpr _ := isJacobsonRing_of_surjective ⟨(e.symm : S →+* R), e.symm.surjective⟩
/-
**isJacobsonRing_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isJacobsonRing_of_isIntegral [Algebra R S] [Algebra.IsIntegral R S] [IsJac
obsonRing R] : IsJacobsonRing S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isJacobsonRing_iff_prime_eq`：isJacobsonRing_iff_prime_eq : IsJacobsonRin
g R ↔ forall P : Ideal R, IsPrime P -> P.jacobson = P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.comap_eq_top_iff`：comap_eq_top_iff {I : Ideal S} : I.comap f = ⊤ ↔
 I = ⊤
· 使用定理 `Ideal.jacobson_top`：jacobson_top : jacobson (⊤ : Ideal R) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.Quotient.nontrivial_iff`：∀ {R : Type u_3} [inst : Ring R] {I : Ide
al R}, Nontrivial (R ⧸ I) ↔ I ≠ ⊤
· 使用定理 `Ideal.jacobson_eq_iff_jacobson_quotient_eq_bot`：jacobson_eq_iff_jacobson
_quotient_eq_bot : I.jacobson = I ↔ jacobson (⊥ : Ideal (R ⧸ I)) = ⊥
· 使用定理 `Ideal.eq_bot_of_comap_eq_bot`：eq_bot_of_comap_eq_bot [Nontrivial R] [IsD
omain S] [Algebra.IsIntegral R S] (hI : I.comap (algebraMap R S) = ⊥) : I = ⊥
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_isPrime`：comap_isPrime [H : IsPrime K] : IsPrime (comap f K)
· 使用定理 `Ideal.comap_jacobson`：comap_jacobson {f : R ->+* S} {K : Ideal S} : coma
p f K.jacobson = sInf (comap f '' { J : Ideal S | K <= J ∧ J.IsMaximal })
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Ideal.exists_ideal_over_maximal_of_isIntegral`：exists_ideal_over_maximal
_of_isIntegral [Algebra.IsIntegral R S] (P : Ideal R) [P_max : IsMaximal P] (hP 
: RingHom.ker (algebraMap R S) <= P…
· 使用定理 `Ideal.comap_bot_le_of_injective`：comap_bot_le_of_injective (hf : Functio
n.Injective f) : comap f ⊥ <= I
· 使用定理 `Ideal.algebraMap_quotient_injective`：algebraMap_quotient_injective {R} [
CommRing R] {I : Ideal A} [I.IsTwoSided] [Algebra R A] : Function.Injective (alg
ebraMap (R ⧸ I.comap (alg…
-/
theorem isJacobsonRing_of_isIntegral [Algebra R S] [Algebra.IsIntegral R S] [IsJacobsonRing R] :
    IsJacobsonRing S := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hP_top : comap (algebraMap R S) P = ⊤
  · simp [comap_eq_top_iff.1 hP_top]
  have : Nontrivial (R ⧸ comap (algebraMap R S) P) := by rwa [Quotient.nontrivial_iff]
  rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
  refine eq_bot_of_comap_eq_bot (R := R ⧸ comap (algebraMap R S) P) ?_
  rw [eq_bot_iff, ← jacobson_eq_iff_jacobson_quotient_eq_bot.1
    ((isJacobsonRing_iff_prime_eq.1 ‹_›) (comap (algebraMap R S) P) (comap_isPrime _ _)),
    comap_jacobson]
  refine sInf_le_sInf fun J hJ => ?_
  simp only [true_and, Set.mem_image, bot_le, Set.mem_ofPred_eq]
  have : J.IsMaximal := by simpa using hJ
  exact exists_ideal_over_maximal_of_isIntegral J
    (comap_bot_le_of_injective _ algebraMap_quotient_injective)

/-- A variant of `isJacobsonRing_of_isIntegral` that takes `RingHom.IsIntegral` instead. -/
/-
**isJacobsonRing_of_isIntegral'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isJacobsonRing_of_isIntegral' (f : R ->+* S) (hf : f.IsIntegral) [IsJacobs
onRing R] : IsJacobsonRing S
参数：f : R ->+* S；hf : f.IsIntegral。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isJacobsonRing_of_isIntegral`：isJacobsonRing_of_isIntegral [Algebra R S]
 [Algebra.IsIntegral R S] [IsJacobsonRing R] : IsJacobsonRing S

--- 原说明 ---
A variant of `isJacobsonRing_of_isIntegral` that takes `RingHom.IsIntegral` inst
ead.
-/
theorem isJacobsonRing_of_isIntegral' (f : R →+* S) (hf : f.IsIntegral) [IsJacobsonRing R] :
    IsJacobsonRing S :=
  let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isJacobsonRing_of_isIntegral (R := R)

end IsJacobsonRing

section Localization

open IsLocalization Submonoid

variable {R S : Type*} [CommRing R] [CommRing S]
variable (y : R) [Algebra R S] [IsLocalization.Away y S]

variable (S) in
/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its comap.
See `le_relIso_of_maximal` for the more general relation isomorphism -/
/-
**IsLocalization.isMaximal_iff_isMaximal_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.isMaximal_iff_isMaximal_disjoint [H : IsJacobsonRing R] (J 
: Ideal S) : J.IsMaximal ↔ (J.under R).IsMaximal ∧ y ∉ J.under R
参数：J : Ideal S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.isPrime_iff_isPrime_disjoint`：isPrime_iff_isPrime_disjoin
t (J : Ideal S) : J.IsPrime ↔ (J.under R).IsPrime ∧ Disjoint (M : Set R) (J.unde
r R)
· 使用定理 `Submonoid.mem_powers`：mem_powers (n : M) : n in powers n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
· 使用定理 `Submodule.mem_toAddSubmonoid`：mem_toAddSubmonoid (p : Submodule R M) (x 
: M) : x in p.toAddSubmonoid ↔ x in p
· 使用定理 `Ideal.jacobson.eq_1`：∀ {R : Type u} [inst : Ring R] (I : Ideal R), I.jac
obson = sInf {J | I ≤ J ∧ J.IsMaximal}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsJacobsonRing.out`：IsJacobsonRing.out {R} [CommRing R] : IsJacobsonRing
 R -> forall {I : Ideal R}, I.IsRadical -> I.jacobson = I
· 使用定理 `Ideal.IsPrime.isRadical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ide
al R}, I.IsPrime → I.IsRadical
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `IsLocalization.under_map_of_isPrime_disjoint`：under_map_of_isPrime_disjo
int {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) : (Ideal.map (a
lgebraMap R S) I).under R = I
· 使用定理 `Ideal.disjoint_powers_iff_notMem_of_isPrime`：disjoint_powers_iff_notMem_
of_isPrime [I.IsPrime] (y : R) : Disjoint (Submonoid.powers y : Set R) ↑I ↔ y ∉ 
I
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalization.isPrime_of_isPrime_disjoint`：isPrime_of_isPrime_disjoint 
(I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) : (Ideal.map (alge
braMap R S) I).IsPrime
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `IsLocalization.map_under`：map_under (J : Ideal S) : Ideal.map (algebraMa
p R S) (J.under R) = J
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its c
omap.
See `le_relIso_of_maximal` for the more general relation isomorphism
-/
theorem IsLocalization.isMaximal_iff_isMaximal_disjoint [H : IsJacobsonRing R] (J : Ideal S) :
    J.IsMaximal ↔ (J.under R).IsMaximal ∧ y ∉ J.under R := by
  constructor
  · refine fun h => ⟨?_, fun hy =>
      h.ne_top (Ideal.eq_top_of_isUnit_mem _ hy (map_units _ ⟨y, Submonoid.mem_powers _⟩))⟩
    have hJ : J.IsPrime := IsMaximal.isPrime h
    rw [isPrime_iff_isPrime_disjoint (Submonoid.powers y)] at hJ
    have : y ∉ (J.under R).1 := Set.disjoint_left.1 hJ.right (Submonoid.mem_powers _)
    rw [← H.out hJ.left.isRadical, jacobson, Submodule.mem_toAddSubmonoid, Ideal.mem_sInf] at this
    push Not at this
    rcases this with ⟨I, ⟨hJI, hIm⟩, hI'⟩
    convert! hIm
    by_cases hJ : J = I.map (algebraMap R S)
    · rw [hJ, under_map_of_isPrime_disjoint (powers y) S hIm.isPrime]
      rwa [disjoint_powers_iff_notMem_of_isPrime]
    · have hI_p : (I.map (algebraMap R S)).IsPrime := by
        refine isPrime_of_isPrime_disjoint (powers y) _ I hIm.isPrime ?_
        rwa [disjoint_powers_iff_notMem_of_isPrime]
      have : J ≤ I.map (algebraMap R S) := map_under (Submonoid.powers y) S J ▸ map_mono hJI
      exact absurd (h.1.2 _ (lt_of_le_of_ne this hJ)) hI_p.1
  · simp only [Ideal.mem_comap, and_imp]
    exact (fun _ _ ↦ IsMaximal.of_isLocalization_of_disjoint (powers y))

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its map.
See `le_relIso_of_maximal` for the more general statement, and the reverse of this implication -/
/-
**IsLocalization.isMaximal_of_isMaximal_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.isMaximal_of_isMaximal_disjoint [IsJacobsonRing R] (I : Ide
al R) (hI : I.IsMaximal) (hy : y ∉ I) : (I.map (algebraMap R S)).IsMaximal
参数：I : Ideal R；hI : I.IsMaximal；hy : y ∉ I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.isMaximal_iff_isMaximal_disjoint`：IsLocalization.isMaxima
l_iff_isMaximal_disjoint [H : IsJacobsonRing R] (J : Ideal S) : J.IsMaximal ↔ (J
.under R).IsMaximal ∧ y ∉ J.under R
· 使用定理 `IsLocalization.under_map_of_isPrime_disjoint`：under_map_of_isPrime_disjo
int {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) : (Ideal.map (a
lgebraMap R S) I).under R = I
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Ideal.disjoint_powers_iff_notMem_of_isPrime`：disjoint_powers_iff_notMem_
of_isPrime [I.IsPrime] (y : R) : Disjoint (Submonoid.powers y : Set R) ↑I ↔ y ∉ 
I
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime

--- 原说明 ---
If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its m
ap.
See `le_relIso_of_maximal` for the more general statement, and the reverse of th
is implication
-/
theorem IsLocalization.isMaximal_of_isMaximal_disjoint
    [IsJacobsonRing R] (I : Ideal R) (hI : I.IsMaximal)
    (hy : y ∉ I) : (I.map (algebraMap R S)).IsMaximal := by
  rw [isMaximal_iff_isMaximal_disjoint S y, under_map_of_isPrime_disjoint (powers y) S hI.isPrime]
  · exact ⟨hI, hy⟩
  · rwa [disjoint_powers_iff_notMem_of_isPrime]

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y` -/
/-
**IsLocalization.orderIsoOfMaximal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocalization.orderIsoOfMaximal [IsJacobsonRing R] : { p : Ideal S // p.I
sMaximal } ≃o { p : Ideal R // p.IsMaximal ∧ y ∉ p } where toFun p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`
-/
def IsLocalization.orderIsoOfMaximal [IsJacobsonRing R] :
    { p : Ideal S // p.IsMaximal } ≃o { p : Ideal R // p.IsMaximal ∧ y ∉ p } where
  toFun p := ⟨Ideal.comap (algebraMap R S) p.1, (isMaximal_iff_isMaximal_disjoint S y p.1).1 p.2⟩
  invFun p := ⟨Ideal.map (algebraMap R S) p.1, isMaximal_of_isMaximal_disjoint y p.1 p.2.1 p.2.2⟩
  left_inv J := Subtype.ext (map_under (powers y) S J)
  right_inv := fun ⟨_, hIm, hI⟩ ↦ Subtype.ext <| under_map_of_isPrime_disjoint _ S hIm.isPrime
    ((disjoint_powers_iff_notMem_of_isPrime y).2 hI)
  map_rel_iff' {I I'} := ⟨fun h => show I.val ≤ I'.val from
    map_under (powers y) S I.val ▸ map_under (powers y) S I'.val ▸ Ideal.map_mono h,
    fun h _ hx => h hx⟩

include y in
/-- If `S` is the localization of the Jacobson ring `R` at the submonoid generated by `y : R`, then
`S` is Jacobson. -/
/-
**isJacobsonRing_localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isJacobsonRing_localization [H : IsJacobsonRing R] : IsJacobsonRing S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isJacobsonRing_iff_prime_eq`：isJacobsonRing_iff_prime_eq : IsJacobsonRin
g R ↔ forall P : Ideal R, IsPrime P -> P.jacobson = P
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.isPrime_iff_isPrime_disjoint`：isPrime_iff_isPrime_disjoin
t (J : Ideal S) : J.IsPrime ↔ (J.under R).IsPrime ∧ Disjoint (M : Set R) (J.unde
r R)
· 使用定理 `IsJacobsonRing.out`：IsJacobsonRing.out {R} [CommRing R] : IsJacobsonRing
 R -> forall {I : Ideal R}, I.IsRadical -> I.jacobson = I
· 使用定理 `Ideal.IsPrime.isRadical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ide
al R}, I.IsPrime → I.IsRadical
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `IsLocalization.map_under`：map_under (J : Ideal S) : Ideal.map (algebraMa
p R S) (J.under R) = J
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `Ideal.jacobson.eq_1`：∀ {R : Type u} [inst : Ring R] (I : Ideal R), I.jac
obson = sInf {J | I ≤ J ∧ J.IsMaximal}
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Submonoid.mem_powers`：mem_powers (n : M) : n in powers n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Ideal.under_def`：under_def : P.under A = Ideal.comap (algebraMap A B) P
· 使用定理 `Ideal.comap_sInf'`：comap_sInf' (s : Set (Ideal S)) : (sInf s).comap f = 
⨅ I in comap f '' s, I
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
· 使用定理 `iInf_le_iInf_of_subset`：∀ {α : Type u_1} {β : Type u_2} [inst : Complete
Lattice α] {f : β → α} {s t : Set β},   s ⊆ t → ⨅ x ∈ t, f x ≤ ⨅ x ∈ s, f x
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.isMaximal_of_isMaximal_disjoint`：IsLocalization.isMaximal
_of_isMaximal_disjoint [IsJacobsonRing R] (I : Ideal R) (hI : I.IsMaximal) (hy :
 y ∉ I) : (I.map (algebraMap R S)).I…
· 使用定理 `IsLocalization.under_map_of_isPrime_disjoint`：under_map_of_isPrime_disjo
int {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) : (Ideal.map (a
lgebraMap R S) I).under R = I
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If `S` is the localization of the Jacobson ring `R` at the submonoid generated b
y `y : R`, then
`S` is Jacobson.
-/
theorem isJacobsonRing_localization [H : IsJacobsonRing R] : IsJacobsonRing S := by
  rw [isJacobsonRing_iff_prime_eq]
  refine fun P' hP' => le_antisymm ?_ le_jacobson
  obtain ⟨hP', hPM⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint (powers y) S P').mp hP'
  have hP := H.out hP'.isRadical
  refine (IsLocalization.map_under (powers y) S P'.jacobson).ge.trans
    ((map_mono ?_).trans (IsLocalization.map_under (powers y) S P').le)
  have : sInf { I : Ideal R | comap (algebraMap R S) P' ≤ I ∧ I.IsMaximal ∧ y ∉ I } ≤
      comap (algebraMap R S) P' := by
    intro x hx
    have hxy : x * y ∈ (comap (algebraMap R S) P').jacobson := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      intro J hJ
      by_cases h : y ∈ J
      · exact J.mul_mem_left x h
      · exact J.mul_mem_right y ((mem_sInf.1 hx) ⟨hJ.left, ⟨hJ.right, h⟩⟩)
    rw [hP] at hxy
    rcases hP'.mem_or_mem hxy with hxy | hxy
    · exact hxy
    · exact (hPM.le_bot ⟨Submonoid.mem_powers _, hxy⟩).elim
  refine le_trans ?_ this
  rw [Ideal.jacobson, under_def, comap_sInf', sInf_eq_iInf]
  refine iInf_le_iInf_of_subset fun I ⟨hI, hIm, hyI⟩ => ⟨map (algebraMap R S) I, ⟨?_, ?_⟩⟩
  · exact ⟨le_trans (IsLocalization.map_under (powers y) S P').symm.le (map_mono hI),
      isMaximal_of_isMaximal_disjoint y I hIm hyI⟩
  · exact IsLocalization.under_map_of_isPrime_disjoint _ S hIm.isPrime <|
      (disjoint_powers_iff_notMem_of_isPrime y).2 hyI

end Localization

namespace Polynomial

section CommRing

-- Porting note: move to better place
/-
**Polynomial.mem_closure_X_union_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mem_closure_X_union_C {R : Type*} [Ring R] (p : R[X]) : p in Subring.closu
re (insert X {f | f.degree <= 0} : Set R[X])
参数：p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `Subring.add_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) 
{x y : R}, x ∈ s → y ∈ s → x + y ∈ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Subring.mul_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) 
{x y : R}, x ∈ s → y ∈ s → x * y ∈ s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
lemma mem_closure_X_union_C {R : Type*} [Ring R] (p : R[X]) :
    p ∈ Subring.closure (insert X {f | f.degree ≤ 0} : Set R[X]) := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro r
    apply Subring.subset_closure
    apply Set.mem_insert_of_mem
    exact degree_C_le
  · intro p1 p2 h1 h2
    exact Subring.add_mem _ h1 h2
  · intro n r hr
    rw [pow_succ, ← mul_assoc]
    apply Subring.mul_mem _ hr
    apply Subring.subset_closure
    apply Set.mem_insert

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
variable {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ]

/-- If `I` is a prime ideal of `R[X]` and `pX ∈ I` is a non-constant polynomial,
  then the map `R →+* R[x]/I` descends to an integral map when localizing at `pX.leadingCoeff`.
  In particular `X` is integral because it satisfies `pX`, and constants are trivially integral,
  so integrality of the entire extension follows by closure under addition and multiplication. -/
/-
**Polynomial.isIntegral_isLocalization_polynomial_quotient** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial`。
形式化陈述：isIntegral_isLocalization_polynomial_quotient (P : Ideal R[X]) (pX : R[X])
 (hpX : pX in P) [Algebra (R ⧸ P.comap (C : R ->+* R[X])) Rₘ] [IsLocalization.Aw
ay (pX.map (Ideal.Quotient.mk (P.comap (C : R ->+* R[X])))).leadingCoeff Rₘ] [Al
gebra (R[X] ⧸ P) Sₘ] [IsLocalization ((Submonoid.powers (pX.map (Ideal.Quotient.
mk (P.comap (C : R ->+* R[X])))).leadingCoeff).map (quotientMap P C le_rfl) : Su
bmonoid (R[X] ⧸ P)) Sₘ] : (IsLocalization.map Sₘ (quotientMap P C le_rfl) (Submo
noid.powers (pX.map (Ideal
参数：P : Ideal R[X]；pX : R[X]；hpX : pX in P；R ⧸ P.comap (C : R ->+* R[X])；pX.map (
Ideal.Quotient.mk (P.comap (C : R ->+* R[X])))；R[X] ⧸ P；(Submonoid.powers (pX.ma
p (Ideal.Quotient.mk (P.comap (C : R ->+* R[X])))).leadingCoeff).map (quotientMa
p P C le_rfl) : Submonoid (R[X] ⧸ P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `IsIntegral.of_mem_closure''`：IsIntegral.of_mem_closure'' {S : Type*} [Co
mmRing S] {f : R ->+* S} (G : Set S) (hG : forall x in G, f.IsIntegralElem x) : 
forall x in Subri…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.isIntegralElem_localization_at_leadingCoeff`：RingHom.isIntegralE
lem_localization_at_leadingCoeff {R S : Type*} [CommSemiring R] [CommSemiring S]
 (f : R ->+* S) (x : S) (p : R[X]) (hf : …
· 使用定理 `Polynomial.eval₂_map`：eval₂_map [Semiring T] (g : S ->+* T) (x : T) : (p
.map f).eval₂ g x = p.eval₂ (g.comp f) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.hom_eval₂`：hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.c
omp f) (g x)
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Polynomial.eval₂_C_X`：eval₂_C_X : eval₂ C X p = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.degree_le_zero_iff`：degree_le_zero_iff : degree p <= 0 ↔ p = 
C (coeff p 0)
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Polynomial.eval₂_sub`：eval₂_sub {S} [Ring S] (f : R ->+* S) {x : S} : (p
 - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `Ideal.quotientMap_mk`：quotientMap_mk {J : Ideal R} {I : Ideal S} [I.IsTw
oSided] [J.IsTwoSided] {f : R ->+* S} {H : J <= I.comap f} {x : R} : quotientMap
 I f H (Qu…
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If `I` is a prime ideal of `R[X]` and `pX ∈ I` is a non-constant polynomial,
  then the map `R →+* R[x]/I` descends to an integral map when localizing at `pX
.leadingCoeff`.
  In particular `X` is integral because it satisfies `pX`, and constants are tri
vially integral,
  so integrality of the entire extension follows by closure under addition and m
ultiplication.
-/
theorem isIntegral_isLocalization_polynomial_quotient
    (P : Ideal R[X]) (pX : R[X]) (hpX : pX ∈ P) [Algebra (R ⧸ P.comap (C : R →+* R[X])) Rₘ]
    [IsLocalization.Away (pX.map (Ideal.Quotient.mk (P.comap (C : R →+* R[X])))).leadingCoeff Rₘ]
    [Algebra (R[X] ⧸ P) Sₘ] [IsLocalization ((Submonoid.powers (pX.map (Ideal.Quotient.mk (P.comap
      (C : R →+* R[X])))).leadingCoeff).map (quotientMap P C le_rfl) : Submonoid (R[X] ⧸ P)) Sₘ] :
    (IsLocalization.map Sₘ (quotientMap P C le_rfl) (Submonoid.powers (pX.map (Ideal.Quotient.mk
      (P.comap (C : R →+* R[X])))).leadingCoeff).le_comap_map : Rₘ →+* Sₘ).IsIntegral := by
  let P' : Ideal R := P.comap C
  let M : Submonoid (R ⧸ P') :=
    Submonoid.powers (pX.map (Ideal.Quotient.mk (P.comap (C : R →+* R[X])))).leadingCoeff
  let M' : Submonoid (R[X] ⧸ P) :=
    (Submonoid.powers (pX.map (Ideal.Quotient.mk (P.comap (C : R →+* R[X])))).leadingCoeff).map
      (quotientMap P C le_rfl)
  let φ : R ⧸ P' →+* R[X] ⧸ P := quotientMap P C le_rfl
  let φ' : Rₘ →+* Sₘ := IsLocalization.map Sₘ φ M.le_comap_map
  have hφ' : φ.comp (Ideal.Quotient.mk P') = (Ideal.Quotient.mk P).comp C := rfl
  intro p
  obtain ⟨⟨p', ⟨q, hq⟩⟩, hp⟩ := IsLocalization.surj M' p
  suffices φ'.IsIntegralElem (algebraMap (R[X] ⧸ P) Sₘ p') by
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨q'', hq''⟩ := isUnit_iff_exists_inv'.1 (IsLocalization.map_units Rₘ (⟨q', hq'⟩ : M))
    refine (hp.symm ▸ this).of_mul_unit φ' p (algebraMap (R[X] ⧸ P) Sₘ (φ q')) q'' ?_
    rw [← φ'.map_one, ← congr_arg φ' hq'', φ'.map_mul, ← φ'.comp_apply]
    simp only [φ', IsLocalization.map_comp _, RingHom.comp_apply]
  dsimp at hp
  refine @IsIntegral.of_mem_closure'' Rₘ _ Sₘ _ φ'
    ((algebraMap (R[X] ⧸ P) Sₘ).comp (Ideal.Quotient.mk P) '' insert X { p | p.degree ≤ 0 }) ?_
    ((algebraMap (R[X] ⧸ P) Sₘ) p') ?_
  · rintro x ⟨p, hp, rfl⟩
    push _ ∈ _ at hp
    rcases hp with hy | hy
    · rw [hy]
      refine φ.isIntegralElem_localization_at_leadingCoeff ((Ideal.Quotient.mk P) X)
        (pX.map (Ideal.Quotient.mk P')) ?_ M ?_
      · rwa [eval₂_map, hφ', ← hom_eval₂, Quotient.eq_zero_iff_mem, eval₂_C_X]
      · use 1
        simp only [P', pow_one]
    · rw [degree_le_zero_iff] at hy
      rw [hy]
      refine ⟨X - C (algebraMap _ _ ((Ideal.Quotient.mk P') (p.coeff 0))), monic_X_sub_C _, ?_⟩
      simp only [eval₂_sub, eval₂_X, eval₂_C]
      rw [sub_eq_zero, ← φ'.comp_apply]
      simp [φ', IsLocalization.map_comp _, P', φ]
  · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p'
    rw [← RingHom.comp_apply]
    apply Subring.mem_closure_image_of
    apply Polynomial.mem_closure_X_union_C

/-- If `f : R → S` descends to an integral map in the localization at `x`,
  and `R` is a Jacobson ring, then the intersection of all maximal ideals in `S` is trivial -/
/-
**Polynomial.jacobson_bot_of_integral_localization** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：jacobson_bot_of_integral_localization {R : Type*} [CommRing R] [IsDomain R
] [IsJacobsonRing R] (Rₘ Sₘ : Type*) [CommRing Rₘ] [CommRing Sₘ] (φ : R ->+* S) 
(hφ : Function.Injective ↑φ) (x : R) (hx : x != 0) [Algebra R Rₘ] [IsLocalizatio
n.Away x Rₘ] [Algebra S Sₘ] [IsLocalization ((Submonoid.powers x).map φ : Submon
oid S) Sₘ] (hφ' : RingHom.IsIntegral (IsLocalization.map Sₘ φ (Submonoid.powers 
x).le_comap_map : Rₘ ->+* Sₘ)) : (⊥ : Ideal S).jacobson = (⊥ : Ideal S)
参数：Rₘ Sₘ : Type*；φ : R ->+* S；hφ : Function.Injective ↑φ；x : R；hx : x != 0；(Subm
onoid.powers x).map φ : Submonoid S；hφ' : RingHom.IsIntegral (IsLocalization.map
 Sₘ φ (Submonoid.powers x).le_comap_map : Rₘ ->+* Sₘ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `map_le_nonZeroDivisors_of_injective`：map_le_nonZeroDivisors_of_injective
 [NoZeroDivisors M₀'] [MonoidWithZeroHomClass F M₀ M₀'] (f : F) (hf : Injective 
f) {S : Submonoid M₀} (hS…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `powers_le_nonZeroDivisors_of_noZeroDivisors`：powers_le_nonZeroDivisors_o
f_noZeroDivisors (hx : x != 0) : Submonoid.powers x <= M₀⁰
· 使用定理 `IsLocalization.isDomain_of_le_nonZeroDivisors`：isDomain_of_le_nonZeroDiv
isors (hM : M <= nonZeroDivisors R) : IsDomain S where __ : IsCancelMulZero S
· 使用定理 `Ideal.comap_isPrime`：comap_isPrime [H : IsPrime K] : IsPrime (comap f K)
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'`：isMaximal_comap_of_is
Integral_of_isMaximal' {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) (h
f : f.IsIntegral) (I : Ideal S) [I.IsMa…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.isMaximal_iff_isMaximal_disjoint`：IsLocalization.isMaxima
l_iff_isMaximal_disjoint [H : IsJacobsonRing R] (J : Ideal S) : J.IsMaximal ↔ (J
.under R).IsMaximal ∧ y ∉ J.under R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `Ideal.under_def`：under_def : P.under A = Ideal.comap (algebraMap A B) P
· 使用定理 `Ideal.bot_quotient_isMaximal_iff`：bot_quotient_isMaximal_iff (I : Ideal 
R) [I.IsTwoSided] : (⊥ : Ideal (R ⧸ I)).IsMaximal ↔ I.IsMaximal
· 使用定理 `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap'`：isMaximal_of_isIntegr
al_of_isMaximal_comap' (f : R ->+* S) (hf : f.IsIntegral) (I : Ideal S) [I.IsPri
me] (hI : IsMaximal (I.comap f)) : IsMa…
· 使用定理 `RingHom.IsIntegral.tower_bot`：∀ {R : Type u_1} {S : Type u_4} {T : Type 
u_5} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   (f : R →+
* S) (g : S →+* T)…
· 使用定理 `Ideal.quotientMap_injective`：quotientMap_injective {I : Ideal S} {f : R 
->+* S} [I.IsTwoSided] : Function.Injective (quotientMap I f le_rfl)
· 使用定理 `Ideal.instIsTwoSidedComap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : 
Ideal S} [inst_…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : R → S` descends to an integral map in the localization at `x`,
  and `R` is a Jacobson ring, then the intersection of all maximal ideals in `S`
 is trivial
-/
theorem jacobson_bot_of_integral_localization
    {R : Type*} [CommRing R] [IsDomain R] [IsJacobsonRing R]
    (Rₘ Sₘ : Type*) [CommRing Rₘ] [CommRing Sₘ] (φ : R →+* S) (hφ : Function.Injective ↑φ) (x : R)
    (hx : x ≠ 0) [Algebra R Rₘ] [IsLocalization.Away x Rₘ] [Algebra S Sₘ]
    [IsLocalization ((Submonoid.powers x).map φ : Submonoid S) Sₘ]
    (hφ' :
      RingHom.IsIntegral (IsLocalization.map Sₘ φ (Submonoid.powers x).le_comap_map : Rₘ →+* Sₘ)) :
    (⊥ : Ideal S).jacobson = (⊥ : Ideal S) := by
  have hM : ((Submonoid.powers x).map φ : Submonoid S) ≤ nonZeroDivisors S :=
    map_le_nonZeroDivisors_of_injective φ hφ (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  let : IsDomain Sₘ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  let φ' : Rₘ →+* Sₘ := IsLocalization.map _ φ (Submonoid.powers x).le_comap_map
  suffices ∀ I : Ideal Sₘ, I.IsMaximal → (I.comap (algebraMap S Sₘ)).IsMaximal by
    have hϕ' : comap (algebraMap S Sₘ) (⊥ : Ideal Sₘ) = (⊥ : Ideal S) := by
      rw [← RingHom.ker_eq_comap_bot, ← RingHom.injective_iff_ker_eq_bot]
      exact IsLocalization.injective Sₘ hM
    have hRₘ : IsJacobsonRing Rₘ := isJacobsonRing_localization x
    have hSₘ : IsJacobsonRing Sₘ := isJacobsonRing_of_isIntegral' φ' hφ'
    refine eq_bot_iff.mpr (le_trans ?_ (le_of_eq hϕ'))
    rw [← hSₘ.out isRadical_bot, comap_jacobson]
    exact sInf_le_sInf fun j hj => ⟨bot_le,
      let ⟨J, hJ⟩ := hj
      hJ.2 ▸ this J hJ.1.2⟩
  intro I hI
  -- Remainder of the proof is pulling and pushing ideals around the square and the quotient square
  have : (I.comap (algebraMap S Sₘ)).IsPrime := comap_isPrime _ I
  have : (I.comap φ').IsPrime := comap_isPrime φ' I
  have : (⊥ : Ideal (S ⧸ I.comap (algebraMap S Sₘ))).IsPrime := isPrime_bot
  have hcomm : φ'.comp (algebraMap R Rₘ) = (algebraMap S Sₘ).comp φ := IsLocalization.map_comp _
  let f := quotientMap (I.comap (algebraMap S Sₘ)) φ le_rfl
  let g := quotientMap I (algebraMap S Sₘ) le_rfl
  have := isMaximal_comap_of_isIntegral_of_isMaximal' φ' hφ' I
  have := ((IsLocalization.isMaximal_iff_isMaximal_disjoint Rₘ x _).1 this).left
  have : ((I.comap (algebraMap S Sₘ)).comap φ).IsMaximal := by
    rwa [under_def, comap_comap, hcomm, ← comap_comap] at this
  rw [← bot_quotient_isMaximal_iff] at this ⊢
  refine isMaximal_of_isIntegral_of_isMaximal_comap' f ?_ ⊥
    ((eq_bot_iff.2 (comap_bot_le_of_injective f quotientMap_injective)).symm ▸ this)
  apply RingHom.IsIntegral.tower_bot f g quotientMap_injective
  rw [comp_quotientMap_eq_of_comp_eq hcomm]
  refine RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ ?_) (hφ'.quotient _)
  apply IsLocalization.surjective_quotientMap_of_maximal_of_localization (Submonoid.powers x)
  rwa [under_def, comap_comap, hcomm, ← bot_quotient_isMaximal_iff]

/-- Used to bootstrap the proof of `isJacobsonRing_polynomial_iff_isJacobsonRing`.
  That theorem is more general and should be used instead of this one. -/
/-
**Polynomial.isJacobsonRing_polynomial_of_domain** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Used to bootstrap the proof of `isJacobsonRing_polynomial_iff_isJacobsonRing`.
  That theorem is more general and should be used instead of this one.
-/
private theorem isJacobsonRing_polynomial_of_domain (R : Type*) [CommRing R] [IsDomain R]
    [hR : IsJacobsonRing R] (P : Ideal R[X]) [IsPrime P] (hP : ∀ x : R, C x ∈ P → x = 0) :
    P.jacobson = P := by
  by_cases Pb : P = ⊥
  · exact Pb.symm ▸
      jacobson_bot_polynomial_of_jacobson_bot (hR.out isRadical_bot)
  · rw [jacobson_eq_iff_jacobson_quotient_eq_bot]
    let P' := P.comap (C : R →+* R[X])
    have : P'.IsPrime := comap_isPrime C P
    have hR' : IsJacobsonRing (R ⧸ P') := by infer_instance
    obtain ⟨p, pP, p0⟩ := exists_nonzero_mem_of_ne_bot Pb hP
    let x := (Polynomial.map (Ideal.Quotient.mk P') p).leadingCoeff
    have hx : x ≠ 0 := by rwa [Ne, leadingCoeff_eq_zero]
    let φ : R ⧸ P' →+* R[X] ⧸ P := Ideal.quotientMap P (C : R →+* R[X]) le_rfl
    let hφ : Function.Injective ↑φ := quotientMap_injective
    let Rₘ := Localization.Away x
    let Sₘ := (Localization ((Submonoid.powers x).map φ : Submonoid (R[X] ⧸ P)))
    refine jacobson_bot_of_integral_localization (S := R[X] ⧸ P) (R := R ⧸ P') Rₘ Sₘ _ hφ _ hx ?_
    exact isIntegral_isLocalization_polynomial_quotient P p pP
/-
**Polynomial.isJacobsonRing_polynomial_of_isJacobsonRing** 是 Mathlib 中的一个定理，位于命名
空间 `Polynomial`。
形式化陈述：isJacobsonRing_polynomial_of_isJacobsonRing (hR : IsJacobsonRing R) : IsJa
cobsonRing R[X]
参数：hR : IsJacobsonRing R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isJacobsonRing_iff_prime_eq`：isJacobsonRing_iff_prime_eq : IsJacobsonRin
g R ↔ forall P : Ideal R, IsPrime P -> P.jacobson = P
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `RingHom.rangeRestrict_surjective`：rangeRestrict_surjective (f : R ->+* S
) : Function.Surjective f.rangeRestrict
· 使用定理 `Ideal.polynomial_mem_ideal_of_coeff_mem_ideal`：polynomial_mem_ideal_of_c
oeff_mem_ideal (I : Ideal R[X]) (p : R[X]) (hp : forall n : Nat, p.coeff n in I.
comap (C : R ->+* R[X])) : p in I
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `isJacobsonRing_of_surjective`：isJacobsonRing_of_surjective [H : IsJacobs
onRing R] : (exists f : R ->+* S, Function.Surjective ↑f) -> IsJacobsonRing S
· 使用定理 `Polynomial.map_surjective`：map_surjective (hf : Function.Surjective f) :
 Function.Surjective (map f)
· 使用定理 `Ideal.map_isPrime_of_surjective`：map_isPrime_of_surjective {f : F} (hf :
 Function.Surjective f) {I : Ideal R} [H : IsPrime I] (hk : RingHom.ker f <= I) 
: IsPrime (map f I)
· 使用定理 `_private.Mathlib.RingTheory.Jacobson.Ring.0.Polynomial.isJacobsonRing_po
lynomial_of_domain`：∀ (R : Type u_5) [inst : CommRing R] [IsDomain R] [hR : IsJa
cobsonRing R] (P : Ideal (Polynomial R)) [P.IsPrime],   (∀ (x : R), Polynomial.C
…
· 使用定理 `Subring.instIsDomainSubtypeMem`：∀ {R : Type u_1} [inst : Ring R] [IsDoma
in R] (s : Subring R), IsDomain ↥s
· 使用定理 `Ideal.eq_zero_of_polynomial_mem_map_range`：eq_zero_of_polynomial_mem_map
_range (I : Ideal R[X]) (x : ((Quotient.mk I).comp C).range) (hx : C x in I.map 
(Polynomial.mapRingHom ((Quotie…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `Ideal.map_jacobson_of_surjective`：map_jacobson_of_surjective {f : R ->+*
 S} (hf : Function.Surjective f) : RingHom.ker f <= I -> map f I.jacobson = (map
 f I).jacobson
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Ideal.le_jacobson`：le_jacobson : I <= jacobson I
-/
theorem isJacobsonRing_polynomial_of_isJacobsonRing (hR : IsJacobsonRing R) :
    IsJacobsonRing R[X] := by
  rw [isJacobsonRing_iff_prime_eq]
  intro I hI
  let R' : Subring (R[X] ⧸ I) := ((Ideal.Quotient.mk I).comp C).range
  let i : R →+* R' := ((Ideal.Quotient.mk I).comp C).rangeRestrict
  have hi : Function.Surjective ↑i := ((Ideal.Quotient.mk I).comp C).rangeRestrict_surjective
  have hi' : RingHom.ker (mapRingHom i) ≤ I := by
    intro f hf
    apply polynomial_mem_ideal_of_coeff_mem_ideal I f
    intro n
    replace hf := congrArg (fun g : Polynomial ((Ideal.Quotient.mk I).comp C).range => g.coeff n) hf
    change (Polynomial.map ((Ideal.Quotient.mk I).comp C).rangeRestrict f).coeff n = 0 at hf
    rw [coeff_map, Subtype.ext_iff] at hf
    rwa [mem_comap, ← Quotient.eq_zero_iff_mem, ← RingHom.comp_apply]
  have R'_jacob : IsJacobsonRing R' := isJacobsonRing_of_surjective ⟨i, hi⟩
  let J := I.map (mapRingHom i)
  have h_surj : Function.Surjective (mapRingHom i) := Polynomial.map_surjective i hi
  have : IsPrime J := map_isPrime_of_surjective h_surj hi'
  suffices h : J.jacobson = J by
    replace h := congrArg (comap (Polynomial.mapRingHom i)) h
    rw [← map_jacobson_of_surjective h_surj hi', comap_map_of_surjective _ h_surj,
      comap_map_of_surjective _ h_surj] at h
    refine le_antisymm ?_ le_jacobson
    exact le_trans (le_sup_of_le_left le_rfl) (le_trans (le_of_eq h) (sup_le le_rfl hi'))
  apply isJacobsonRing_polynomial_of_domain R' J
  exact eq_zero_of_polynomial_mem_map_range I
/-
**Polynomial.isJacobsonRing_polynomial_iff_isJacobsonRing** 是 Mathlib 中的一个定理，位于命
名空间 `Polynomial`。
形式化陈述：isJacobsonRing_polynomial_iff_isJacobsonRing : IsJacobsonRing R[X] ↔ IsJac
obsonRing R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isJacobsonRing_of_surjective`：isJacobsonRing_of_surjective [H : IsJacobs
onRing R] : (exists f : R ->+* S, Function.Surjective ↑f) -> IsJacobsonRing S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.isJacobsonRing_polynomial_of_isJacobsonRing`：isJacobsonRing_p
olynomial_of_isJacobsonRing (hR : IsJacobsonRing R) : IsJacobsonRing R[X]
-/
theorem isJacobsonRing_polynomial_iff_isJacobsonRing : IsJacobsonRing R[X] ↔ IsJacobsonRing R := by
  refine ⟨?_, isJacobsonRing_polynomial_of_isJacobsonRing⟩
  intro H
  exact isJacobsonRing_of_surjective ⟨eval₂RingHom (RingHom.id _) 1, fun x =>
    ⟨C x, by simp only [coe_eval₂RingHom, RingHom.id_apply, eval₂_C]⟩⟩
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsJacobsonRing R] : IsJacobsonRing R[X] :=
  isJacobsonRing_polynomial_iff_isJacobsonRing.mpr ‹IsJacobsonRing R›

end CommRing

section

variable {R : Type*} [CommRing R]
variable (P : Ideal R[X]) [hP : P.IsMaximal]

/-
**Polynomial.isMaximal_comap_C_of_isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：isMaximal_comap_C_of_isMaximal [IsJacobsonRing R] [Nontrivial R] (hP' : fo
rall x : R, C x in P -> x = 0) : IsMaximal (comap (C : R ->+* R[X]) P : Ideal R)
参数：hP' : forall x : R, C x in P -> x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_isPrime`：comap_isPrime [H : IsPrime K] : IsPrime (comap f K)
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Submodule.nonzero_mem_of_bot_lt`：nonzero_mem_of_bot_lt {p : Submodule R 
M} (bot_lt : ⊥ < p) : exists a : p, a != 0
· 使用定理 `Ideal.bot_lt_of_maximal`：bot_lt_of_maximal (M : Ideal R) [hm : M.IsMaxim
al] (non_field : ¬IsField R) : ⊥ < M
· 使用定理 `Polynomial.not_isField`：∀ (R : Type u) [inst : Ring R], ¬IsField (Polyno
mial R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.bot_quotient_isMaximal_iff`：bot_quotient_isMaximal_iff (I : Ideal 
R) [I.IsTwoSided] : (⊥ : Ideal (R ⧸ I)).IsMaximal ↔ I.IsMaximal
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.quotientMap_injective`：quotientMap_injective {I : Ideal S} {f : R 
->+* S} [I.IsTwoSided] : Function.Injective (quotientMap I f le_rfl)
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `Ideal.instIsTwoSidedComap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : 
Ideal S} [inst_…
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `Ideal.map_bot`：map_bot : (⊥ : Ideal R).map f = ⊥
（共 46 条，此处仅展示前 30 条）
-/
theorem isMaximal_comap_C_of_isMaximal [IsJacobsonRing R] [Nontrivial R]
    (hP' : ∀ x : R, C x ∈ P → x = 0) :
    IsMaximal (comap (C : R →+* R[X]) P : Ideal R) := by
  let P' := comap (C : R →+* R[X]) P
  have hP'_prime : P'.IsPrime := comap_isPrime C P
  obtain ⟨⟨m, hmem_P⟩, hm⟩ :=
    Submodule.nonzero_mem_of_bot_lt (bot_lt_of_maximal P (Polynomial.not_isField R))
  have hm' : m ≠ 0 := by
    simpa [Submodule.coe_eq_zero] using hm
  let φ : R ⧸ P' →+* R[X] ⧸ P := quotientMap P (C : R →+* R[X]) le_rfl
  let a : R ⧸ P' := (m.map (Ideal.Quotient.mk P')).leadingCoeff
  let M : Submonoid (R ⧸ P') := Submonoid.powers a
  rw [← bot_quotient_isMaximal_iff]
  have hp0 : a ≠ 0 := fun hp0' =>
    hm' <| map_injective (Ideal.Quotient.mk (P.comap (C : R →+* R[X]) : Ideal R))
      ((injective_iff_map_eq_zero (Ideal.Quotient.mk (P.comap (C : R →+* R[X]) : Ideal R))).2
        fun x hx => by
          rwa [Quotient.eq_zero_iff_mem, (by rwa [eq_bot_iff] : (P.comap C : Ideal R) = ⊥)] at hx)
        (by simpa only [a, leadingCoeff_eq_zero, Polynomial.map_zero] using hp0')
  have hM : (0 : R ⧸ P') ∉ M := fun ⟨n, hn⟩ => hp0 (eq_zero_of_pow_eq_zero hn)
  suffices (⊥ : Ideal (Localization M)).IsMaximal by
    rw [← IsLocalization.under_map_of_isPrime_disjoint M (Localization M) isPrime_bot
      (disjoint_iff_inf_le.mpr fun x hx => hM (hx.2 ▸ hx.1))]
    exact ((IsLocalization.isMaximal_iff_isMaximal_disjoint (Localization M) a _).mp
      (by rwa [Ideal.map_bot])).1
  let M' : Submonoid (R[X] ⧸ P) := M.map φ
  have hM' : (0 : R[X] ⧸ P) ∉ M' := fun ⟨z, hz⟩ =>
    hM (quotientMap_injective (_root_.trans hz.2 φ.map_zero.symm) ▸ hz.1)
  suffices (⊥ : Ideal (Localization M')).IsMaximal by
    rw [le_antisymm bot_le (comap_bot_le_of_injective _
      (IsLocalization.map_injective_of_injective M (Localization M) (Localization M')
        quotientMap_injective))]
    refine isMaximal_comap_of_isIntegral_of_isMaximal' _ ?_ ⊥
    have isloc : IsLocalization (Submonoid.map φ M) (Localization M') := by infer_instance
    exact @isIntegral_isLocalization_polynomial_quotient R _
      (Localization M) (Localization M') _ _ P m hmem_P _ _ _ isloc
  rw [(map_bot.symm :
    (⊥ : Ideal (Localization M')) = Ideal.map (algebraMap (R[X] ⧸ P) (Localization M')) ⊥)]
  let bot_maximal := (bot_quotient_isMaximal_iff _).mpr hP
  refine bot_maximal.map_bijective (algebraMap (R[X] ⧸ P) (Localization M')) ?_
  apply IsField.localization_map_bijective hM'
  rwa [← Quotient.maximal_ideal_iff_isField_quotient, ← bot_quotient_isMaximal_iff]

/-- Used to bootstrap the more general `quotient_mk_comp_C_isIntegral_of_jacobson` -/
/-
**Polynomial.quotient_mk_comp_C_isIntegral_of_jacobson'** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Used to bootstrap the more general `quotient_mk_comp_C_isIntegral_of_jacobson`
-/
private theorem quotient_mk_comp_C_isIntegral_of_jacobson' [Nontrivial R] (hR : IsJacobsonRing R)
    (hP' : ∀ x : R, C x ∈ P → x = 0) :
    ((Ideal.Quotient.mk P).comp C : R →+* R[X] ⧸ P).IsIntegral := by
  refine (isIntegral_quotientMap_iff _).mp ?_
  let P' : Ideal R := P.comap C
  obtain ⟨pX, hpX, hp0⟩ := exists_nonzero_mem_of_ne_bot
    (ne_of_lt (bot_lt_of_maximal P (Polynomial.not_isField R))).symm hP'
  let a : R ⧸ P' := (pX.map (Ideal.Quotient.mk P')).leadingCoeff
  let M : Submonoid (R ⧸ P') := Submonoid.powers a
  let φ : R ⧸ P' →+* R[X] ⧸ P := quotientMap P C le_rfl
  have hP'_prime : P'.IsPrime := comap_isPrime C P
  have hM : (0 : R ⧸ P') ∉ M := fun ⟨n, hn⟩ =>
    hp0 <| leadingCoeff_eq_zero.mp (eq_zero_of_pow_eq_zero hn)
  let M' : Submonoid (R[X] ⧸ P) := M.map φ
  refine RingHom.IsIntegral.tower_bot φ (algebraMap _ (Localization M')) ?_ ?_
  · refine IsLocalization.injective (Localization M')
      (show M' ≤ _ from le_nonZeroDivisors_of_noZeroDivisors fun hM' => hM ?_)
    exact
      let ⟨z, zM, z0⟩ := hM'
      quotientMap_injective (_root_.trans z0 φ.map_zero.symm) ▸ zM
  · suffices RingHom.comp (algebraMap (R[X] ⧸ P) (Localization M')) φ =
      (IsLocalization.map (Localization M') φ M.le_comap_map).comp
        (algebraMap (R ⧸ P') (Localization M)) by
      rw [this]
      refine RingHom.IsIntegral.trans (algebraMap (R ⧸ P') (Localization M))
        (IsLocalization.map (Localization M') φ M.le_comap_map) ?_ ?_
      · exact (algebraMap (R ⧸ P') (Localization M)).isIntegral_of_surjective
          (IsField.localization_map_bijective hM ((Quotient.maximal_ideal_iff_isField_quotient _).mp
            (isMaximal_comap_C_of_isMaximal P hP'))).2
      · -- `convert` here is faster than `exact`, and this proof is near the time limit.
        -- convert isIntegral_isLocalization_polynomial_quotient P pX hpX
        have isloc : IsLocalization M' (Localization M') := by infer_instance
        exact @isIntegral_isLocalization_polynomial_quotient R _
          (Localization M) (Localization M') _ _ P pX hpX _ _ _ isloc
    rw [IsLocalization.map_comp M.le_comap_map]

variable [IsJacobsonRing R]

/-- If `R` is a Jacobson ring, and `P` is a maximal ideal of `R[X]`,
  then `R → R[X]/P` is an integral map. -/
/-
**Polynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing** 是 Mathlib 中的一个定理，
位于命名空间 `Polynomial`。
形式化陈述：quotient_mk_comp_C_isIntegral_of_isJacobsonRing : ((Ideal.Quotient.mk P).c
omp C : R ->+* R[X] ⧸ P).IsIntegral
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_isPrime`：comap_isPrime [H : IsPrime K] : IsPrime (comap f K)
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Polynomial.map_surjective`：map_surjective (hf : Function.Surjective f) :
 Function.Surjective (map f)
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Ideal.polynomial_mem_ideal_of_coeff_mem_ideal`：polynomial_mem_ideal_of_c
oeff_mem_ideal (I : Ideal R[X]) (p : R[X]) (hp : forall n : Nat, p.coeff n in I.
comap (C : R ->+* R[X])) : p in I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.ext_iff`：ext_iff {p q : R[X]} : p = q ↔ forall n, coeff p n =
 coeff q n
· 使用定理 `RingHom.IsIntegral.tower_bot`：∀ {R : Type u_1} {S : Type u_4} {T : Type 
u_5} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   (f : R →+
* S) (g : S →+* T)…
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f
· 使用定理 `Ideal.injective_quotient_le_comap_map`：injective_quotient_le_comap_map (
P : Ideal R[X]) : Function.Injective Ideal.quotientMap (Ideal.map (Polynomial.ma
pRingHom (Quotient.mk (P.co…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.quotient_mk_maps_eq`：quotient_mk_maps_eq (P : Ideal R[X]) : ((Quot
ient.mk (map (mapRingHom (Quotient.mk (P.comap (C : R ->+* R[X])))) P)).comp C).
comp (Quotient.…
· 使用定理 `RingHom.IsIntegral.trans`：∀ {R : Type u_1} {S : Type u_4} {T : Type u_5}
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   (f : R →+* S)
 (g : S →+* T)…
· 使用定理 `RingHom.isIntegral_of_surjective`：RingHom.isIntegral_of_surjective (hf :
 Function.Surjective f) : f.IsIntegral
· 使用定理 `Ideal.map_eq_top_or_isMaximal_of_surjective`：map_eq_top_or_isMaximal_of_
surjective (hf : Function.Surjective f) {I : Ideal R} (H : IsMaximal I) : map f 
I = ⊤ ∨ IsMaximal (map f I)
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If `R` is a Jacobson ring, and `P` is a maximal ideal of `R[X]`,
  then `R → R[X]/P` is an integral map.
-/
theorem quotient_mk_comp_C_isIntegral_of_isJacobsonRing :
    ((Ideal.Quotient.mk P).comp C : R →+* R[X] ⧸ P).IsIntegral := by
  let P' : Ideal R := P.comap C
  have : P'.IsPrime := comap_isPrime C P
  let f : R[X] →+* Polynomial (R ⧸ P') := Polynomial.mapRingHom (Ideal.Quotient.mk P')
  have hf : Function.Surjective ↑f := map_surjective (Ideal.Quotient.mk P') Quotient.mk_surjective
  have hPJ : P = (P.map f).comap f := by
    rw [comap_map_of_surjective _ hf]
    refine le_antisymm (le_sup_of_le_left le_rfl) (sup_le le_rfl ?_)
    refine fun p hp =>
      polynomial_mem_ideal_of_coeff_mem_ideal P p fun n => Quotient.eq_zero_iff_mem.mp ?_
    simpa only [f, coeff_map, coe_mapRingHom] using! (Polynomial.ext_iff.mp hp) n
  refine RingHom.IsIntegral.tower_bot
    (T := (R ⧸ comap C P)[X] ⧸ _) _ _ (injective_quotient_le_comap_map P) ?_
  rw [← quotient_mk_maps_eq]
  refine ((Ideal.Quotient.mk P').isIntegral_of_surjective Quotient.mk_surjective).trans _ _ ?_
  have : IsMaximal (Ideal.map (mapRingHom (Ideal.Quotient.mk (comap C P))) P) :=
    Or.recOn (map_eq_top_or_isMaximal_of_surjective f hf hP)
      (fun h => absurd (_root_.trans (h ▸ hPJ : P = comap f ⊤) comap_top : P = ⊤) hP.ne_top) id
  apply quotient_mk_comp_C_isIntegral_of_jacobson' _ ?_ (fun x hx => ?_)
  any_goals exact isJacobsonRing_quotient
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rwa [Quotient.eq_zero_iff_mem, mem_comap, hPJ, mem_comap, coe_mapRingHom, map_C]
/-
**Polynomial.isMaximal_comap_C_of_isJacobsonRing** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：isMaximal_comap_C_of_isJacobsonRing : (P.comap (C : R ->+* R[X])).IsMaxima
l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.bot_quotient_isMaximal_iff`：bot_quotient_isMaximal_iff (I : Ideal 
R) [I.IsTwoSided] : (⊥ : Ideal (R ⧸ I)).IsMaximal ↔ I.IsMaximal
· 使用定理 `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'`：isMaximal_comap_of_is
Integral_of_isMaximal' {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) (h
f : f.IsIntegral) (I : Ideal S) [I.IsMa…
· 使用定理 `Polynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing`：quotient_mk_
comp_C_isIntegral_of_isJacobsonRing : ((Ideal.Quotient.mk P).comp C : R ->+* R[X
] ⧸ P).IsIntegral
-/
theorem isMaximal_comap_C_of_isJacobsonRing : (P.comap (C : R →+* R[X])).IsMaximal := by
  rw [← @mk_ker _ _ P, RingHom.ker_eq_comap_bot, comap_comap]
  have := (bot_quotient_isMaximal_iff _).mpr hP
  exact isMaximal_comap_of_isIntegral_of_isMaximal' _
    (quotient_mk_comp_C_isIntegral_of_isJacobsonRing P) ⊥
/-
**Polynomial.comp_C_integral_of_surjective_of_isJacobsonRing** 是 Mathlib 中的一个定理，
位于命名空间 `Polynomial`。
形式化陈述：comp_C_integral_of_surjective_of_isJacobsonRing {S : Type*} [Field S] (f :
 R[X] ->+* S) (hf : Function.Surjective ↑f) : (f.comp C).IsIntegral
参数：f : R[X] ->+* S；hf : Function.Surjective ↑f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ker_isMaximal_of_surjective`：ker_isMaximal_of_surjective {R K F 
: Type*} [Ring R] [DivisionRing K] [FunLike F R K] [RingHomClass F R K] (f : F) 
(hf : Function.Surjective…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Polynomial.ringHom_ext'`：ringHom_ext' {S} [Semiring S] {f g : R[X] ->+* 
S} (h₁ : f.comp C = g.comp C) (h₂ : f X = g X) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `RingHom.IsIntegral.trans`：∀ {R : Type u_1} {S : Type u_4} {T : Type u_5}
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   (f : R →+* S)
 (g : S →+* T)…
· 使用定理 `Polynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing`：quotient_mk_
comp_C_isIntegral_of_isJacobsonRing : ((Ideal.Quotient.mk P).comp C : R ->+* R[X
] ⧸ P).IsIntegral
· 使用定理 `RingHom.isIntegral_of_surjective`：RingHom.isIntegral_of_surjective (hf :
 Function.Surjective f) : f.IsIntegral
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `RingHom.coe_comp`：coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp
 hmn : α -> γ) = hnp ∘ hmn
-/
theorem comp_C_integral_of_surjective_of_isJacobsonRing {S : Type*} [Field S] (f : R[X] →+* S)
    (hf : Function.Surjective ↑f) : (f.comp C).IsIntegral := by
  have : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  let g : R[X] ⧸ (RingHom.ker f) →+* S := Ideal.Quotient.lift (RingHom.ker f) f fun _ h => h
  have hfg : g.comp (Ideal.Quotient.mk (RingHom.ker f)) = f := ringHom_ext' rfl rfl
  rw [← hfg, RingHom.comp_assoc]
  refine (quotient_mk_comp_C_isIntegral_of_isJacobsonRing (RingHom.ker f)).trans _ g
    (g.isIntegral_of_surjective ?_)
  rw [← hfg, RingHom.coe_comp] at hf
  exact Function.Surjective.of_comp hf

end

end Polynomial

open MvPolynomial RingHom

namespace MvPolynomial

/-
**MvPolynomial.isJacobsonRing_MvPolynomial_fin** 是 Mathlib 中的一个定理，位于命名空间 `MvPoly
nomial`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [H : IsJacobsonRing R] (n : ℕ), IsJacob
sonRing (MvPolynomial (Fin n) R)
参数：n : ℕ；MvPolynomial (Fin n) R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isJacobsonRing_MvPolynomial_fin {R : Type u} [CommRing R] [H : IsJacobsonRing R] :
    ∀ n : ℕ, IsJacobsonRing (MvPolynomial (Fin n) R)
  | 0 => (isJacobsonRing_iso ((renameEquiv R (Equiv.equivPEmpty (Fin 0))).toRingEquiv.trans
    (isEmptyRingEquiv R PEmpty.{u + 1}))).mpr H
  | n + 1 => (isJacobsonRing_iso (finSuccEquiv R n).toRingEquiv).2
    (Polynomial.isJacobsonRing_polynomial_iff_isJacobsonRing.2 (isJacobsonRing_MvPolynomial_fin n))

/-- General form of the Nullstellensatz for Jacobson rings, since in a Jacobson ring we have
  `Inf {P maximal | P ≥ I} = Inf {P prime | P ≥ I} = I.radical`. Fields are always Jacobson,
  and in that special case this is (most of) the classical Nullstellensatz,
  since `I(V(I))` is the intersection of maximal ideals containing `I`, which is then `I.radical` -/
/-
**MvPolynomial.isJacobsonRing** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
形式化陈述：isJacobsonRing {R : Type*} [CommRing R] {ι : Type*} [Finite ι] [IsJacobson
Ring R] : IsJacobsonRing (MvPolynomial ι R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isJacobsonRing_iso`：isJacobsonRing_iso (e : R ≃+* S) : IsJacobsonRing R 
↔ IsJacobsonRing S where mp _
· 使用定理 `MvPolynomial.isJacobsonRing_MvPolynomial_fin`：∀ {R : Type u} [inst : Com
mRing R] [H : IsJacobsonRing R] (n : ℕ), IsJacobsonRing (MvPolynomial (Fin n) R)

--- 原说明 ---
General form of the Nullstellensatz for Jacobson rings, since in a Jacobson ring
 we have
  `Inf {P maximal | P ≥ I} = Inf {P prime | P ≥ I} = I.radical`. Fields are alwa
ys Jacobson,
  and in that special case this is (most of) the classical Nullstellensatz,
  since `I(V(I))` is the intersection of maximal ideals containing `I`, which is
 then `I.radical`
-/
instance isJacobsonRing {R : Type*} [CommRing R] {ι : Type*} [Finite ι] [IsJacobsonRing R] :
    IsJacobsonRing (MvPolynomial ι R) := by
  cases nonempty_fintype ι
  let e := Fintype.equivFin ι
  rw [isJacobsonRing_iso (renameEquiv R e).toRingEquiv]
  exact isJacobsonRing_MvPolynomial_fin _

variable {n : ℕ}

universe v w

/-- The constant coefficient as an R-linear morphism -/
/-
**MvPolynomial.C** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：C : R ->+* MvPolynomial σ R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant coefficient as an R-linear morphism
-/
private noncomputable def Cₐ (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : S →ₐ[R] S[X] :=
  { Polynomial.C with commutes' := fun r => by rfl }
/-
**MvPolynomial.aux_IH** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_IH {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [IsJacobsonRing S] [Algebra R S] [Algebra R T]
    (IH : ∀ (Q : Ideal S), (IsMaximal Q) → RingHom.IsIntegral (algebraMap R (S ⧸ Q)))
    (v : S[X] ≃ₐ[R] T) (P : Ideal T) (hP : P.IsMaximal) :
    RingHom.IsIntegral (algebraMap R (T ⧸ P)) := by
  let Q := P.comap v.toAlgHom.toRingHom
  have hw : Ideal.map v Q = P := map_comap_of_surjective v v.surjective P
  have hQ : IsMaximal Q := comap_isMaximal_of_surjective _ v.surjective
  let w : (S[X] ⧸ Q) ≃ₐ[R] (T ⧸ P) := Ideal.quotientEquivAlg Q P v hw.symm
  let Q' := Q.comap (Polynomial.C)
  let w' : (S ⧸ Q') →ₐ[R] (S[X] ⧸ Q) := Ideal.quotientMapₐ Q (Cₐ R S) le_rfl
  have h_eq : algebraMap R (T ⧸ P) =
    w.toRingEquiv.toRingHom.comp (w'.toRingHom.comp (algebraMap R (S ⧸ Q'))) := by
    ext r
    simp only [AlgHom.toRingHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower, coe_comp, coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes]
  rw [h_eq]
  apply RingHom.IsIntegral.trans
  · apply RingHom.IsIntegral.trans
    · apply IH
      apply Polynomial.isMaximal_comap_C_of_isJacobsonRing
    · suffices w'.toRingHom = Ideal.quotientMap Q (Polynomial.C) le_rfl by
        rw [this]
        rw [isIntegral_quotientMap_iff _]
        apply Polynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing
      rfl
  · apply RingHom.isIntegral_of_surjective
    exact w.surjective
/-
**MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing'** 是 Mathlib 中的一个
定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem quotient_mk_comp_C_isIntegral_of_isJacobsonRing'
    {R : Type*} [CommRing R] [IsJacobsonRing R]
    (P : Ideal (MvPolynomial (Fin n) R)) (hP : P.IsMaximal) :
    RingHom.IsIntegral (algebraMap R (MvPolynomial (Fin n) R ⧸ P)) := by
  induction n with
  | zero =>
    apply RingHom.isIntegral_of_surjective
    apply Function.Surjective.comp Quotient.mk_surjective
    exact C_surjective (Fin 0)
  | succ n IH => apply aux_IH IH (finSuccEquiv R n).symm P hP
/-
**MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing** 是 Mathlib 中的一个定
理，位于命名空间 `MvPolynomial`。
形式化陈述：quotient_mk_comp_C_isIntegral_of_isJacobsonRing {R : Type*} [CommRing R] [
IsJacobsonRing R] (P : Ideal (MvPolynomial (Fin n) R)) [hP : P.IsMaximal] : Ring
Hom.IsIntegral (RingHom.comp (Ideal.Quotient.mk P) (MvPolynomial.C))
参数：P : Ideal (MvPolynomial (Fin n) R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `_private.Mathlib.RingTheory.Jacobson.Ring.0.MvPolynomial.quotient_mk_com
p_C_isIntegral_of_isJacobsonRing'`：∀ {n : ℕ} {R : Type u_1} [inst : CommRing R] 
[IsJacobsonRing R] (P : Ideal (MvPolynomial (Fin n) R)),   P.IsMaximal → (algebr
aMap R (MvPolyn…
-/
theorem quotient_mk_comp_C_isIntegral_of_isJacobsonRing {R : Type*} [CommRing R] [IsJacobsonRing R]
    (P : Ideal (MvPolynomial (Fin n) R)) [hP : P.IsMaximal] :
    RingHom.IsIntegral (RingHom.comp (Ideal.Quotient.mk P) (MvPolynomial.C)) := by
  change RingHom.IsIntegral (algebraMap R (MvPolynomial (Fin n) R ⧸ P))
  apply quotient_mk_comp_C_isIntegral_of_isJacobsonRing'
  infer_instance
/-
**MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing** 是 Mathlib 中的一个定
理，位于命名空间 `MvPolynomial`。
形式化陈述：comp_C_integral_of_surjective_of_isJacobsonRing {R : Type*} [CommRing R] [
IsJacobsonRing R] {σ : Type*} [Finite σ] {S : Type*} [Field S] (f : MvPolynomial
 σ R ->+* S) (hf : Function.Surjective ↑f) : (f.comp C).IsIntegral
参数：f : MvPolynomial σ R ->+* S；hf : Function.Surjective ↑f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `RingHom.ker_isMaximal_of_surjective`：ker_isMaximal_of_surjective {R K F 
: Type*} [Ring R] [DivisionRing K] [FunLike F R K] [RingHomClass F R K] (f : F) 
(hf : Function.Surjective…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `MvPolynomial.ringHom_ext`：ringHom_ext {A : Type*} [Semiring A] {f g : Mv
Polynomial σ R ->+* A} (hC : forall r, f (C r) = g (C r)) (hX : forall i, f (X i
) = g (X i)) :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `RingHom.IsIntegral.trans`：∀ {R : Type u_1} {S : Type u_4} {T : Type u_5}
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   (f : R →+* S)
 (g : S →+* T)…
· 使用定理 `MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing`：quotient_m
k_comp_C_isIntegral_of_isJacobsonRing {R : Type*} [CommRing R] [IsJacobsonRing R
] (P : Ideal (MvPolynomial (Fin n) R)) [hP : P.IsM…
· 使用定理 `RingHom.isIntegral_of_surjective`：RingHom.isIntegral_of_surjective (hf :
 Function.Surjective f) : f.IsIntegral
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `RingHom.coe_comp`：coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp
 hmn : α -> γ) = hnp ∘ hmn
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgEquiv.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A
] [inst_…
-/
theorem comp_C_integral_of_surjective_of_isJacobsonRing {R : Type*} [CommRing R] [IsJacobsonRing R]
    {σ : Type*} [Finite σ] {S : Type*} [Field S] (f : MvPolynomial σ R →+* S)
    (hf : Function.Surjective ↑f) : (f.comp C).IsIntegral := by
  cases nonempty_fintype σ
  have e := (Fintype.equivFin σ).symm
  let f' : MvPolynomial (Fin _) R →+* S := f.comp (renameEquiv R e).toRingEquiv.toRingHom
  have hf' := Function.Surjective.comp hf (renameEquiv R e).surjective
  change Function.Surjective ↑f' at hf'
  have : (f'.comp C).IsIntegral := by
    have : (RingHom.ker f').IsMaximal := ker_isMaximal_of_surjective f' hf'
    let g : MvPolynomial _ R ⧸ (RingHom.ker f') →+* S :=
      Ideal.Quotient.lift (RingHom.ker f') f' fun _ h => h
    have hfg : g.comp (Ideal.Quotient.mk (RingHom.ker f')) = f' :=
      ringHom_ext (fun r => rfl) fun i => rfl
    rw [← hfg, RingHom.comp_assoc]
    refine (quotient_mk_comp_C_isIntegral_of_isJacobsonRing (RingHom.ker f')).trans _ g
      (g.isIntegral_of_surjective ?_)
    rw [← hfg, coe_comp] at hf'
    exact Function.Surjective.of_comp hf'
  rw [RingHom.comp_assoc] at this
  convert! this
  refine RingHom.ext fun x => ?_
  exact ((renameEquiv R e).commutes' x).symm

end MvPolynomial

/-
**isJacobsonRing_of_finiteType** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isJacobsonRing_of_finiteType {A B : Type*} [CommRing A] [CommRing B] [Alge
bra A B] [IsJacobsonRing A] [Algebra.FiniteType A B] : IsJacobsonRing B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FiniteType.iff_quotient_mvPolynomial'`：iff_quotient_mvPolynomial
' : FiniteType R S ↔ exists (ι : Type uS) (_ : Fintype ι) (f : MvPolynomial ι R 
->ₐ[R] S), Surjective f
· 使用定理 `isJacobsonRing_of_surjective`：isJacobsonRing_of_surjective [H : IsJacobs
onRing R] : (exists f : R ->+* S, Function.Surjective ↑f) -> IsJacobsonRing S
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma isJacobsonRing_of_finiteType {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsJacobsonRing A] [Algebra.FiniteType A B] : IsJacobsonRing B := by
  obtain ⟨ι, hι, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp ‹_›
  exact isJacobsonRing_of_surjective ⟨f.toRingHom, hf⟩
/-
**RingHom.FiniteType.isJacobsonRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.FiniteType.isJacobsonRing {A B : Type*} [CommRing A] [CommRing B] 
{f : A ->+* B} [IsJacobsonRing A] (H : f.FiniteType) : IsJacobsonRing B
参数：H : f.FiniteType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isJacobsonRing_of_finiteType`：isJacobsonRing_of_finiteType {A B : Type*}
 [CommRing A] [CommRing B] [Algebra A B] [IsJacobsonRing A] [Algebra.FiniteType 
A B] : IsJacobsonR…
-/
lemma RingHom.FiniteType.isJacobsonRing {A B : Type*} [CommRing A] [CommRing B]
    {f : A →+* B} [IsJacobsonRing A] (H : f.FiniteType) : IsJacobsonRing B :=
  @isJacobsonRing_of_finiteType A B _ _ f.toAlgebra _ H

@[stacks 0CY7 "See also https://en.wikipedia.org/wiki/Zariski%27s_lemma."]
/-
**finite_of_finite_type_of_isJacobsonRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finite_of_finite_type_of_isJacobsonRing (R S : Type*) [CommRing R] [Field 
S] [Algebra R S] [IsJacobsonRing R] [Algebra.FiniteType R S] : Module.Finite R S
参数：R S : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FiniteType.iff_quotient_mvPolynomial'`：iff_quotient_mvPolynomial
' : FiniteType R S ↔ exists (ι : Type uS) (_ : Fintype ι) (f : MvPolynomial ι R 
->ₐ[R] S), Surjective f
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing`：comp_C_int
egral_of_surjective_of_isJacobsonRing {R : Type*} [CommRing R] [IsJacobsonRing R
] {σ : Type*} [Finite σ] {S : Type*} [Field S] (f …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Algebra.isIntegral_def`：Algebra.isIntegral_def : Algebra.IsIntegral R A 
↔ forall x : A, IsIntegral R x
· 使用定理 `Algebra.IsIntegral.finite`：Algebra.IsIntegral.finite [Algebra.IsIntegral
 R A] [h' : Algebra.FiniteType R A] : Module.Finite R A
-/
lemma finite_of_finite_type_of_isJacobsonRing (R S : Type*) [CommRing R] [Field S]
    [Algebra R S] [IsJacobsonRing R] [Algebra.FiniteType R S] :
    Module.Finite R S := by
  obtain ⟨ι, hι, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp ‹_›
  have : (algebraMap R S).IsIntegral := by
    rw [← f.comp_algebraMap]
    -- We need to write `f.toRingHom` instead of just `f`, to avoid unification issues.
    exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing f.toRingHom hf
  have : Algebra.IsIntegral R S := Algebra.isIntegral_def.mpr this
  exact Algebra.IsIntegral.finite

/--
If `f : R →+* S` is a ring homomorphism from a Jacobson ring to a field,
then it is finite if and only if it is finite type.
-/
/-
**RingHom.finite_iff_finiteType_of_isJacobsonRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.finite_iff_finiteType_of_isJacobsonRing {R S : Type*} [CommRing R]
 [IsJacobsonRing R] [Field S] {f : R ->+* S} : f.Finite ↔ f.FiniteType
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FiniteType.of_finite`：of_finite {f : A ->+* B} (hf : f.Finite) :
 f.FiniteType
· 使用引理 `finite_of_finite_type_of_isJacobsonRing`：finite_of_finite_type_of_isJaco
bsonRing (R S : Type*) [CommRing R] [Field S] [Algebra R S] [IsJacobsonRing R] [
Algebra.FiniteType R S] : Mod…

--- 原说明 ---
If `f : R →+* S` is a ring homomorphism from a Jacobson ring to a field,
then it is finite if and only if it is finite type.
-/
lemma RingHom.finite_iff_finiteType_of_isJacobsonRing
    {R S : Type*} [CommRing R] [IsJacobsonRing R] [Field S]
    {f : R →+* S} : f.Finite ↔ f.FiniteType :=
  ⟨RingHom.FiniteType.of_finite,
    by intro; algebraize [f]; exact finite_of_finite_type_of_isJacobsonRing R S⟩

/-- If `K` is a Jacobson Noetherian ring, `A` a nontrivial `K`-algebra of finite type,
then any `K`-subfield of `A` is finite over `K`. -/
/-
**finite_of_algHom_finiteType_of_isJacobsonRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finite_of_algHom_finiteType_of_isJacobsonRing {K L A : Type*} [CommRing K]
 [DivisionRing L] [CommRing A] [IsJacobsonRing K] [IsNoetherianRing K] [Nontrivi
al A] [Algebra K L] [Algebra K A] [Algebra.FiniteType K A] (f : L ->ₐ[K] A) : Mo
dule.Finite K L
参数：f : L ->ₐ[K] A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_maximal`：exists_maximal [Nontrivial α] : exists M : Ideal α
, M.IsMaximal
· 使用引理 `finite_of_finite_type_of_isJacobsonRing`：finite_of_finite_type_of_isJaco
bsonRing (R S : Type*) [CommRing R] [Field S] [Algebra R S] [IsJacobsonRing R] [
Algebra.FiniteType R S] : Mod…
· 使用定理 `Module.Finite.of_injective`：∀ {R : Type u_1} {S : Type u_2} {M : Type u_
3} {N : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommM
onoid M] [inst_3…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R

--- 原说明 ---
If `K` is a Jacobson Noetherian ring, `A` a nontrivial `K`-algebra of finite typ
e,
then any `K`-subfield of `A` is finite over `K`.
-/
theorem finite_of_algHom_finiteType_of_isJacobsonRing
    {K L A : Type*} [CommRing K] [DivisionRing L] [CommRing A]
    [IsJacobsonRing K] [IsNoetherianRing K] [Nontrivial A]
    [Algebra K L] [Algebra K A]
    [Algebra.FiniteType K A] (f : L →ₐ[K] A) :
    Module.Finite K L := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let := Ideal.Quotient.field m
  have := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  exact Module.Finite.of_injective ((Ideal.Quotient.mkₐ K m).comp f).toLinearMap
    (RingHom.injective _)

/-- If `K` is a Jacobson Noetherian ring, `A` a nontrivial `K`-algebra of finite type,
then any `K`-subfield of `A` is finite over `K`. -/
nonrec theorem RingHom.finite_of_algHom_finiteType_of_isJacobsonRing
    {K L A : Type*} [CommRing K] [Field L] [CommRing A]
    [IsJacobsonRing K] [IsNoetherianRing K] [Nontrivial A]
    (f : K →+* L) (g : L →+* A) (hfg : (g.comp f).FiniteType) :
    f.Finite := by
  algebraize [f, (g.comp f)]
  exact finite_of_algHom_finiteType_of_isJacobsonRing ⟨g, fun _ ↦ rfl⟩

