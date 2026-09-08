/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Support

import Mathlib.RingTheory.Localization.InvSubmonoid

/-!
# Unramified locus of an algebra

## Main results
- `Algebra.unramifiedLocus` : The set of primes that is unramified over the base.
- `Algebra.basicOpen_subset_unramifiedLocus_iff` :
  `D(f)` is contained in the unramified locus if and only if `A_f` is unramified over `R`.
- `Algebra.unramifiedLocus_eq_univ_iff` :
  The unramified locus is the whole spectrum if and only if `A` is unramified over `R`.
- `Algebra.isOpen_unramifiedLocus` :
  If `A` is (essentially) of finite type over `R`, then the unramified locus is open.
-/

@[expose] public section

universe u

namespace Algebra

section

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]

variable (R) in
/-- We say that an `R`-algebra `A` is unramified at a prime `q` of `A`
if `A_q` is formally unramified over `R`.

If `A` is of finite type over `R` and `q` is lying over `p`, then this is equivalent to
`κ(q)/κ(p)` being separable and `pA_q = qA_q`.
See `Algebra.isUnramifiedAt_iff_map_eq` in `RingTheory.Unramified.LocalRing` -/
/-
**Algebra.IsUnramifiedAt** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra`。
形式化陈述：IsUnramifiedAt (q : Ideal A) [q.IsPrime] : Prop
参数：q : Ideal A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that an `R`-algebra `A` is unramified at a prime `q` of `A`
if `A_q` is formally unramified over `R`.

If `A` is of finite type over `R` and `q` is lying over `p`, then this is equiva
lent to
`κ(q)/κ(p)` being separable and `pA_q = qA_q`.
See `Algebra.isUnramifiedAt_iff_map_eq` in `RingTheory.Unramified.LocalRing`
-/
abbrev IsUnramifiedAt (q : Ideal A) [q.IsPrime] : Prop :=
  FormallyUnramified R (Localization.AtPrime q)

variable (R A) in
/-- `Algebra.unramifiedLocus R A` is the set of primes `p` of `A` that are unramified. -/
/-
**Algebra.unramifiedLocus** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：unramifiedLocus : Set (PrimeSpectrum A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Algebra.unramifiedLocus R A` is the set of primes `p` of `A` that are unramifie
d.
-/
def unramifiedLocus : Set (PrimeSpectrum A) :=
  { p | IsUnramifiedAt R p.asIdeal }
/-
**Algebra.IsUnramifiedAt.comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsUnramifiedAt`
。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : CommRing B]   [inst_3 : Algebra R A] [inst_4 : Algebra 
A B] [inst_5 : Algebra R B] [IsScalarTower R A B] (p : Ideal A) (P : Ideal B)   
[P.LiesOver p] [inst_8 : p.IsPrime] [inst_9 : P.IsPrime] [Algebra.IsUnramifiedAt
 R p] [Algebra.IsUnramifiedAt A P],   Algebra.IsUnramifiedAt R P
参数：p : Ideal A；P : Ideal B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.of_restrictScalars`：of_restrictScalars [Forma
llyUnramified R B] : FormallyUnramified A B
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `Algebra.FormallyUnramified.comp`：comp [FormallyUnramified R A] [Formally
Unramified A B] : FormallyUnramified R B
-/
lemma IsUnramifiedAt.comp
    (p : Ideal A) (P : Ideal B) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsUnramifiedAt R p] [IsUnramifiedAt A P] : IsUnramifiedAt R P := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have : FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime P) :=
    .of_restrictScalars A _ _
  exact FormallyUnramified.comp R (Localization.AtPrime p) _

variable (R) in
/-
**Algebra.IsUnramifiedAt.of_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.I
sUnramifiedAt`。
形式化陈述：∀ (R : Type u_1) {A : Type u_2} {B : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : CommRing B]   [inst_3 : Algebra R A] [inst_4 : Algebra 
A B] [inst_5 : Algebra R B] [IsScalarTower R A B] (P : Ideal B)   [inst_7 : P.Is
Prime] [Algebra.IsUnramifiedAt R P], Algebra.IsUnramifiedAt A P
参数：R : Type u_1；P : Ideal B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.of_restrictScalars`：of_restrictScalars [Forma
llyUnramified R B] : FormallyUnramified A B
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma IsUnramifiedAt.of_restrictScalars (P : Ideal B) [P.IsPrime]
    [IsUnramifiedAt R P] : IsUnramifiedAt A P :=
  FormallyUnramified.of_restrictScalars R _ _
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p] [IsUnramifiedAt R q]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
  .of_restrictScalars R _ _

open _root_.TensorProduct in
/-- If `A` is an `R`-algebra unramified at `Q`, `P` is the prime of `R` lying under `Q`,
then `κ(P) ⊗ A` is unramified at `Q'` (the prime corresponding to `Q`) over `κ(P)`. -/
/-
**Algebra.IsUnramifiedAt.residueField** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsUnram
ifiedAt`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : CommRing A] 
[inst_2 : Algebra R A] (P : Ideal R)   [inst_3 : P.IsPrime] (Q : Ideal A) [inst_
4 : Q.IsPrime] [Q.LiesOver P] [Algebra.IsUnramifiedAt R Q]   (Q' : Ideal (P.Fibe
r A)) [inst_7 : Q'.IsPrime],   Q = Ideal.comap Algebra.TensorProduct.includeRigh
t.toRingHom Q' → Algebra.IsUnramifiedAt P.ResidueField Q'
参数：P : Ideal R；Q : Ideal A；Q' : Ideal (P.Fiber A)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.SurjectiveOnStalks.baseChange'`：∀ {R : Type u_1} [inst : CommRin
g R] {S : Type u_2} [inst_1 : CommRing S] {T : Type u_3} [inst_2 : CommRing T]  
 [inst_3 : Algebra R T] [ins…
· 使用引理 `Ideal.surjectiveOnStalks_residueField`：Ideal.surjectiveOnStalks_residueF
ield (I : Ideal R) [I.IsPrime] : (algebraMap R I.ResidueField).SurjectiveOnStalk
s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.FormallyUnramified.of_surjective`：of_surjective [FormallyUnramif
ied R A] (f : A ->ₐ[R] B) (H : Function.Surjective f) : FormallyUnramified R B

--- 原说明 ---
If `A` is an `R`-algebra unramified at `Q`, `P` is the prime of `R` lying under 
`Q`,
then `κ(P) ⊗ A` is unramified at `Q'` (the prime corresponding to `Q`) over `κ(P
)`.
-/
theorem IsUnramifiedAt.residueField
    (P : Ideal R) [P.IsPrime] (Q : Ideal A) [Q.IsPrime]
    [Q.LiesOver P] [Algebra.IsUnramifiedAt R Q]
    (Q' : Ideal (P.Fiber A)) [Q'.IsPrime]
    (hQ' : Q = Q'.comap Algebra.TensorProduct.includeRight.toRingHom) :
    IsUnramifiedAt P.ResidueField Q' := by
  let f₀ : Localization.AtPrime Q →ₐ[R] Localization.AtPrime Q' :=
    Localization.localAlgHom Q Q' _ hQ'
  have hf₀ : Function.Surjective f₀ := by
    subst hQ'; exact P.surjectiveOnStalks_residueField.baseChange' _ _
  let f : P.Fiber (Localization.AtPrime Q) →ₐ[P.ResidueField] Localization.AtPrime Q' :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) f₀ fun _ _ ↦ .all _ _
  have hf : Function.Surjective f := hf₀.forall.mpr fun x ↦ ⟨1 ⊗ₜ x, by simp [f]⟩
  exact .of_surjective _ hf

end

section IsUnramifiedIn

variable {R : Type*} [CommRing R]

/-- A prime `𝔭` of `R` is unramified in `A` if every prime ideal `𝔓` of `A` lying over `𝔭` is
unramified . -/
/-
**Algebra.IsUnramifiedIn** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：IsUnramifiedIn (A : Type*) [CommRing A] [Algebra R A] (𝔭 : Ideal R) : Prop
参数：A : Type*；𝔭 : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prime `𝔭` of `R` is unramified in `A` if every prime ideal `𝔓` of `A` lying ov
er `𝔭` is
unramified .
-/
def IsUnramifiedIn (A : Type*) [CommRing A] [Algebra R A] (𝔭 : Ideal R) : Prop :=
  ∀ (𝔓 : Ideal A) (_ : 𝔓.IsPrime), 𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt R 𝔓

variable (A : Type*) [CommRing A] [Algebra R A]
/-
**Algebra.isUnramifiedIn_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：isUnramifiedIn_top : IsUnramifiedIn A (⊤ : Ideal R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.eq_top_iff_of_liesOver`：eq_top_iff_of_liesOver [P.LiesOver p] : P 
= ⊤ ↔ p = ⊤
-/
theorem isUnramifiedIn_top : IsUnramifiedIn A (⊤ : Ideal R) :=
  fun P hP _ ↦ (hP.ne_top ((Ideal.eq_top_iff_of_liesOver P (⊤ : Ideal R)).mpr rfl)).elim

end IsUnramifiedIn
section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-
**Algebra.unramifiedLocus_eq_compl_support** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：unramifiedLocus_eq_compl_support : unramifiedLocus R A = (Module.support A
 Ω[A⁄R])ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instSMulCommClass`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Algebra.formallyUnramified_iff`：∀ (R : Type v) (A : Type u) [inst : Comm
Ring R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.FormallyUnramifi
ed R A ↔ Subsingleto…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
-/
lemma unramifiedLocus_eq_compl_support :
    unramifiedLocus R A = (Module.support A Ω[A⁄R])ᶜ := by
  ext p
  simp only [Set.mem_compl_iff, Module.notMem_support_iff]
  have := IsLocalizedModule.iso p.asIdeal.primeCompl
    (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
  exact (Algebra.formallyUnramified_iff _ _).trans this.subsingleton_congr.symm
/-
**Algebra.basicOpen_subset_unramifiedLocus_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a`。
形式化陈述：basicOpen_subset_unramifiedLocus_iff {f : A} : ↑(PrimeSpectrum.basicOpen f
) subseteq unramifiedLocus R A ↔ Algebra.FormallyUnramified R (Localization.Away
 f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.unramifiedLocus_eq_compl_support`：unramifiedLocus_eq_compl_suppo
rt : unramifiedLocus R A = (Module.support A Ω[A⁄R])ᶜ
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LocalizedModule.subsingleton_iff_support_subset`：LocalizedModule.subsing
leton_iff_support_subset {f : R} : Subsingleton (LocalizedModule.Away f M) ↔ Mod
ule.support R M subseteq PrimeSpectru…
· 使用定理 `Algebra.formallyUnramified_iff`：∀ (R : Type v) (A : Type u) [inst : Comm
Ring R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.FormallyUnramifi
ed R A ↔ Subsingleto…
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instSMulCommClass`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
-/
lemma basicOpen_subset_unramifiedLocus_iff {f : A} :
    ↑(PrimeSpectrum.basicOpen f) ⊆ unramifiedLocus R A ↔
      Algebra.FormallyUnramified R (Localization.Away f) := by
  rw [unramifiedLocus_eq_compl_support, Set.subset_compl_comm,
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl,
    ← LocalizedModule.subsingleton_iff_support_subset, Algebra.formallyUnramified_iff]
  exact (IsLocalizedModule.iso (.powers f)
    (KaehlerDifferential.map R R A (Localization.Away f))).subsingleton_congr
/-
**Algebra.unramifiedLocus_eq_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：unramifiedLocus_eq_univ_iff : unramifiedLocus R A = Set.univ ↔ Algebra.For
mallyUnramified R A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.unramifiedLocus_eq_compl_support`：unramifiedLocus_eq_compl_suppo
rt : unramifiedLocus R A = (Module.support A Ω[A⁄R])ᶜ
· 使用定理 `compl_eq_comm`：compl_eq_comm : xᶜ = y ↔ yᶜ = x
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Module.support_eq_empty_iff`：Module.support_eq_empty_iff : Module.suppor
t R M = ∅ ↔ Subsingleton M
· 使用定理 `Algebra.formallyUnramified_iff`：∀ (R : Type v) (A : Type u) [inst : Comm
Ring R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.FormallyUnramifi
ed R A ↔ Subsingleto…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma unramifiedLocus_eq_univ_iff :
    unramifiedLocus R A = Set.univ ↔ Algebra.FormallyUnramified R A := by
  rw [unramifiedLocus_eq_compl_support, compl_eq_comm, Set.compl_univ, eq_comm,
    Module.support_eq_empty_iff, Algebra.formallyUnramified_iff]
/-
**Algebra.formallyUnramified_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：formallyUnramified_iff_forall : FormallyUnramified R A ↔ forall q : PrimeS
pectrum A, IsUnramifiedAt R q.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Algebra.unramifiedLocus_eq_univ_iff`：unramifiedLocus_eq_univ_iff : unram
ifiedLocus R A = Set.univ ↔ Algebra.FormallyUnramified R A
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
-/
theorem formallyUnramified_iff_forall :
    FormallyUnramified R A ↔ ∀ q : PrimeSpectrum A, IsUnramifiedAt R q.1 :=
  unramifiedLocus_eq_univ_iff.symm.trans Set.eq_univ_iff_forall
/-
**Algebra.unramified_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：unramified_iff_forall [FiniteType R A] : Unramified R A ↔ forall q : Prime
Spectrum A, IsUnramifiedAt R q.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.formallyUnramified_iff_forall`：formallyUnramified_iff_forall : F
ormallyUnramified R A ↔ forall q : PrimeSpectrum A, IsUnramifiedAt R q.1
-/
theorem unramified_iff_forall [FiniteType R A] :
    Unramified R A ↔ ∀ q : PrimeSpectrum A, IsUnramifiedAt R q.1 :=
  .trans ⟨fun h ↦ h.formallyUnramified, fun h ↦ ⟨h, inferInstance⟩⟩ formallyUnramified_iff_forall
/-
**Algebra.isOpen_unramifiedLocus** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：isOpen_unramifiedLocus [EssFiniteType R A] : IsOpen (unramifiedLocus R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.unramifiedLocus_eq_compl_support`：unramifiedLocus_eq_compl_suppo
rt : unramifiedLocus R A = (Module.support A Ω[A⁄R])ᶜ
· 使用引理 `Module.support_eq_zeroLocus`：Module.support_eq_zeroLocus : Module.suppor
t R M = zeroLocus (Module.annihilator R M)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `PrimeSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set R) : IsClo
sed (zeroLocus s)
-/
lemma isOpen_unramifiedLocus [EssFiniteType R A] : IsOpen (unramifiedLocus R A) := by
  rw [unramifiedLocus_eq_compl_support, Module.support_eq_zeroLocus]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
/-
**Algebra.exists_formallyUnramified_of_isUnramifiedAt** 是 Mathlib 中的一个引理，位于命名空间 
`Algebra`。
形式化陈述：exists_formallyUnramified_of_isUnramifiedAt [EssFiniteType R A] (p : Ideal
 A) [p.IsPrime] [IsUnramifiedAt R p] : exists f ∉ p, Algebra.FormallyUnramified 
R (Localization.Away f)
参数：p : Ideal A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `PrimeSpectrum.isBasis_basic_opens`：isBasis_basic_opens : TopologicalSpac
e.Opens.IsBasis (Set.range (@basicOpen R _))
· 使用引理 `Algebra.isOpen_unramifiedLocus`：isOpen_unramifiedLocus [EssFiniteType R 
A] : IsOpen (unramifiedLocus R A)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Algebra.basicOpen_subset_unramifiedLocus_iff`：basicOpen_subset_unramifie
dLocus_iff {f : A} : ↑(PrimeSpectrum.basicOpen f) subseteq unramifiedLocus R A ↔
 Algebra.FormallyUnramified R (Loc…
-/
lemma exists_formallyUnramified_of_isUnramifiedAt [EssFiniteType R A] (p : Ideal A) [p.IsPrime]
    [IsUnramifiedAt R p] : ∃ f ∉ p, Algebra.FormallyUnramified R (Localization.Away f) := by
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show ⟨p, ‹_›⟩ ∈ unramifiedLocus R A from ‹_›) isOpen_unramifiedLocus
  exact ⟨r, hpr, basicOpen_subset_unramifiedLocus_iff.mp hr⟩
/-
**Algebra.exists_unramified_of_isUnramifiedAt** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
`。
形式化陈述：exists_unramified_of_isUnramifiedAt [Algebra.FiniteType R A] (p : Ideal A)
 [p.IsPrime] [IsUnramifiedAt R p] : exists f ∉ p, Algebra.Unramified R (Localiza
tion.Away f)
参数：p : Ideal A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.exists_formallyUnramified_of_isUnramifiedAt`：exists_formallyUnra
mified_of_isUnramifiedAt [EssFiniteType R A] (p : Ideal A) [p.IsPrime] [IsUnrami
fiedAt R p] : exists f ∉ p, Algebra.Forma…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Algebra.FiniteType.trans`：trans [Algebra S A] [IsScalarTower R S A] (hRS
 : FiniteType R S) (hSA : FiniteType S A) : FiniteType R A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalization.finiteType_of_monoid_fg`：finiteType_of_monoid_fg [Monoid.
FG M] : Algebra.FiniteType R S
-/
lemma exists_unramified_of_isUnramifiedAt [Algebra.FiniteType R A] (p : Ideal A) [p.IsPrime]
    [IsUnramifiedAt R p] : ∃ f ∉ p, Algebra.Unramified R (Localization.Away f) := by
  obtain ⟨f, hfp, H⟩ := exists_formallyUnramified_of_isUnramifiedAt (R := R) p
  exact ⟨f, hfp, ⟨H, .trans ‹_› (IsLocalization.finiteType_of_monoid_fg (.powers f) _)⟩⟩

end

end Algebra

