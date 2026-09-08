/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.QuasiFinite.Basic

/-!

# Weakly Quasi-finite primes

The definition `Algebra.QuasiFiniteAt` is equivalent to the usual definition "isolated in fibers"
mathematically for algebras of finite type, but this requires Zariski's main theorem to prove.
Hence we introduce a weaker notion of being `Algebra.WeaklyQuasiFiniteAt` that we shall state
Zariski's main theorem in terms of, and deduce from this that `Algebra.WeaklyQuasiFiniteAt` is
equivalent to `Algebra.QuasiFiniteAt` under all relevant scenarios.

This class should only be used in stating (and proving) Zariski's main theorem and should not be
used elsewhere, and all public API shall have a `Algebra.QuasiFiniteAt` version.

## Implementation details

The definition of `Algebra.QuasiFiniteAt R q` as is says that the whole `S_q` is quasi-finite,
which requires not only `q` to be quasi-finite, but also all primes below it (i.e. all generic
points that specialize to it) to also be quasi-finite.
This is fine mathematically because the set of quasi-finite primes is open
(according to Zariski's Main theorem). But this requires the statement of Zariski's main
to be stated with an a priori weaker notion of quasi-finite.
Hence we introduce `Algebra.WeaklyQuasiFiniteAt` where we mod out all the primes that lie in a
different fiber.

-/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T]
variable (p : Ideal R) (q : Ideal S) [q.IsPrime]

variable (R) in
/-- (Implementation) An a priori weaker notion of being quasi-finite at a prime,
which turns out to be equivalent to `Algebra.QuasiFiniteAt` (for finite type algebras)
due to Zariski's main theorem.

This class should not be used outside of this context,
and `Algebra.QuasiFiniteAt` should be used instead.
See `Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt`. -/
/-
**Algebra.WeaklyQuasiFiniteAt** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Algebra.WeaklyQuasiFiniteAt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) An a priori weaker notion of being quasi-finite at a prime,
which turns out to be equivalent to `Algebra.QuasiFiniteAt` (for finite type alg
ebras)
due to Zariski's main theorem.

This class should not be used outside of this context,
and `Algebra.QuasiFiniteAt` should be used instead.
See `Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt`.
-/
abbrev Algebra.WeaklyQuasiFiniteAt :=
  Algebra.QuasiFiniteAt R (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S))))

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.weaklyQuasiFiniteAt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.weaklyQuasiFiniteAt_iff : Algebra.WeaklyQuasiFiniteAt R q ↔ Algebr
a.QuasiFinite R (Localization.AtPrime q ⧸ (q.under R).map (algebraMap R (Localiz
ation.AtPrime q)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.Quotient.instIsPrimeQuotientMapRingHomAlgebraMapMkOfLiesOver`：∀ (R
 : Type u_2) [inst : CommSemiring R] {A : Type u_3} [inst_1 : CommRing A] [inst_
2 : Algebra R A] (p : Ideal R)   (P : Ideal A) [P.IsPrim…
· 使用定理 `RingHom.SurjectiveOnStalks.localRingHom_surjective`：∀ {R : Type u_1} [in
st : CommRing R] {S : Type u_2} [inst_1 : CommRing S] {f : R →+* S},   f.Surject
iveOnStalks →     ∀ (P : Ideal R) [inst_…
· 使用引理 `RingHom.surjectiveOnStalks_of_surjective`：surjectiveOnStalks_of_surjecti
ve (h : Function.Surjective f) : SurjectiveOnStalks f
· 使用引理 `Algebra.QuasiFinite.iff_of_algEquiv`：iff_of_algEquiv (e : S ≃ₐ[R] T) : A
lgebra.QuasiFinite R S ↔ Algebra.QuasiFinite R T
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Localization.le_comap_primeCompl_iff`：le_comap_primeCompl_iff {J : Ideal
 P} [J.IsPrime] {f : R ->+* P} : I.primeCompl <= J.primeCompl.comap f ↔ J.comap 
f <= I
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Localization.localRingHom_mk'`：localRingHom_mk' (J : Ideal P) [J.IsPrime
] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) (y : I.primeCompl) : localRingHom
 I J f hIJ (IsLocal…
（共 41 条，此处仅展示前 30 条）
-/
lemma Algebra.weaklyQuasiFiniteAt_iff :
    Algebra.WeaklyQuasiFiniteAt R q ↔
      Algebra.QuasiFinite R (Localization.AtPrime q ⧸
        (q.under R).map (algebraMap R (Localization.AtPrime q))) := by
  let q' := q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))
  have hq' : q = q'.comap (Ideal.Quotient.mk _) := .trans
    (by simp [← RingHom.ker_eq_comap_bot, Ideal.map_comap_le])
    (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm
  let φ₁ : Localization.AtPrime q →ₐ[R] Localization.AtPrime q' :=
    Localization.localAlgHom _ _ (Ideal.Quotient.mkₐ _ _) hq'
  have hφ₁ : Function.Surjective φ₁ :=
    (RingHom.surjectiveOnStalks_of_surjective
      Ideal.Quotient.mk_surjective).localRingHom_surjective _ _ hq'
  refine Algebra.QuasiFinite.iff_of_algEquiv ((Ideal.quotientEquivAlg _ _ (.refl) ?_).trans
    (Ideal.quotientKerAlgEquivOfSurjective hφ₁)).symm
  ext x
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  simp [φ₁, IsScalarTower.algebraMap_eq R S (Localization.AtPrime q), ← Ideal.map_map,
    IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_eq_zero_iff,
    Ideal.Quotient.mk_surjective.exists, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    ← Ideal.mem_comap, ← hq']

namespace Algebra.WeaklyQuasiFiniteAt

/-
**Algebra.WeaklyQuasiFiniteAt.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.WeaklyQuasiFin
iteAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [QuasiFiniteAt R q] : WeaklyQuasiFiniteAt R q := by
  rw [weaklyQuasiFiniteAt_iff]
  exact .of_surjective_algHom (Ideal.Quotient.mkₐ _ _) Ideal.Quotient.mk_surjective

/-- Use `Algebra.QuasiFinite.of_surjective_algHom` instead for `Algebra.QuasiFiniteAt R p`. -/
/-
**Algebra.WeaklyQuasiFiniteAt.of_algHom_localization** 是 Mathlib 中的一个引理，位于命名空间 `
Algebra.WeaklyQuasiFiniteAt`。
形式化陈述：of_algHom_localization (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p]
 (q : Ideal T) [q.IsPrime] (f : Localization.AtPrime p ->ₐ[R] Localization.AtPri
me q) (hf : Function.Surjective f) : WeaklyQuasiFiniteAt R q
参数：p : Ideal S；q : Ideal T；f : Localization.AtPrime p ->ₐ[R] Localization.AtPrim
e q；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.weaklyQuasiFiniteAt_iff`：Algebra.weaklyQuasiFiniteAt_iff : Algeb
ra.WeaklyQuasiFiniteAt R q ↔ Algebra.QuasiFinite R (Localization.AtPrime q ⧸ (q.
under R).map (algebra…
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IsLocalHom.of_surjective`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRi
ng R] [inst_1 : CommRing S] [Nontrivial S] [IsLocalRing R] (f : R →+* S),   Func
tion.Surjectiv…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `IsLocalHom.map_nonunit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} {
inst : Monoid R} {inst_1 : Monoid S} {inst_2 : FunLike F R S} {f : F}   [self : 
IsLocalHom f…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `IsLocalization.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.AtPrime.isUnit_mk'_iff`：∀ {R : Type u_1} [inst : CommSemi
ring R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (I : Ide
al R)   [hI : I.IsPrime] [i…
· 使用引理 `Algebra.QuasiFinite.of_surjective_algHom`：of_surjective_algHom [QuasiFin
ite R S] (f : S ->ₐ[R] T) (hf : Function.Surjective f) : QuasiFinite R T
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.quotientMap_surjective`：quotientMap_surjective {J : Ideal R} {I : 
Ideal S} [I.IsTwoSided] [J.IsTwoSided] {f : R ->+* S} {H : J <= I.comap f} (hf :
 Function.Surjecti…

--- 原说明 ---
Use `Algebra.QuasiFinite.of_surjective_algHom` instead for `Algebra.QuasiFiniteA
t R p`.
-/
lemma of_algHom_localization (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p]
    (q : Ideal T) [q.IsPrime]
    (f : Localization.AtPrime p →ₐ[R] Localization.AtPrime q) (hf : Function.Surjective f) :
    WeaklyQuasiFiniteAt R q := by
  rw [weaklyQuasiFiniteAt_iff] at *
  have H : (p.under R).map (algebraMap R _) ≤
      ((q.under R).map (algebraMap R _)).comap f.toRingHom := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, AlgHom.toRingHom_eq_coe,
      AlgHom.comp_algebraMap_of_tower]
    grw [← Ideal.le_comap_map]
    intro x hx
    by_contra hx'
    have : IsLocalHom f.toRingHom := .of_surjective _ hf
    have := this.1 (algebraMap _ _ x) (by
      suffices IsUnit (IsLocalization.mk' (M := q.primeCompl) (Localization.AtPrime q)
        (algebraMap _ _ x) 1) by simpa [IsLocalization.mk'_one] using! this
      simpa [IsLocalization.AtPrime.isUnit_mk'_iff])
    exact (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime p) p
      (algebraMap _ _ x) 1).mp (by simpa [IsLocalization.mk'_one]) hx
  exact .of_surjective_algHom (S := Localization.AtPrime p ⧸
    (p.under R).map (algebraMap R (Localization.AtPrime p))) (Ideal.quotientMapₐ _ f H)
    (Ideal.quotientMap_surjective (H := H) hf)

/-- Use `Algebra.QuasiFiniteAt.of_surjectiveOnStalks` instead for `Algebra.QuasiFiniteAt R p`. -/
/-
**Algebra.WeaklyQuasiFiniteAt.of_surjectiveOnStalks** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebra.WeaklyQuasiFiniteAt`。
形式化陈述：of_surjectiveOnStalks (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p] 
(q : Ideal T) [q.IsPrime] (f : S ->ₐ[R] T) (hf : f.SurjectiveOnStalks) (hq : p =
 Ideal.comap f q) : WeaklyQuasiFiniteAt R q
参数：p : Ideal S；q : Ideal T；f : S ->ₐ[R] T；hf : f.SurjectiveOnStalks；hq : p = Ide
al.comap f q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `Algebra.WeaklyQuasiFiniteAt.of_algHom_localization`：of_algHom_localizati
on (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p] (q : Ideal T) [q.IsPrime]
 (f : Localization.AtPrime p ->ₐ[R] Loca…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Use `Algebra.QuasiFiniteAt.of_surjectiveOnStalks` instead for `Algebra.QuasiFini
teAt R p`.
-/
lemma of_surjectiveOnStalks
    (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p] (q : Ideal T) [q.IsPrime]
    (f : S →ₐ[R] T) (hf : f.SurjectiveOnStalks) (hq : p = Ideal.comap f q) :
    WeaklyQuasiFiniteAt R q := by
  subst hq
  exact of_algHom_localization _ _ (Localization.localAlgHom _ _ f rfl) (hf _ _)

/-- By `infer_instance` for `Algebra.QuasiFiniteAt R p`. -/
/-
**Algebra.WeaklyQuasiFiniteAt.comap_algEquiv** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.
WeaklyQuasiFiniteAt`。
形式化陈述：comap_algEquiv (p : Ideal S) [p.IsPrime] [Algebra.WeaklyQuasiFiniteAt R p]
 (f : T ≃ₐ[R] S) : WeaklyQuasiFiniteAt R (p.comap f.toRingHom)
参数：p : Ideal S；f : T ≃ₐ[R] S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.WeaklyQuasiFiniteAt.of_surjectiveOnStalks`：of_surjectiveOnStalks
 (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p] (q : Ideal T) [q.IsPrime] (
f : S ->ₐ[R] T) (hf : f.SurjectiveOnSta…
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用引理 `RingHom.surjectiveOnStalks_of_surjective`：surjectiveOnStalks_of_surjecti
ve (h : Function.Surjective f) : SurjectiveOnStalks f
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
By `infer_instance` for `Algebra.QuasiFiniteAt R p`.
-/
instance comap_algEquiv (p : Ideal S) [p.IsPrime]
    [Algebra.WeaklyQuasiFiniteAt R p]
    (f : T ≃ₐ[R] S) : WeaklyQuasiFiniteAt R (p.comap f.toRingHom) :=
  .of_surjectiveOnStalks p _ f.symm.toAlgHom
    (RingHom.surjectiveOnStalks_of_surjective f.symm.surjective) (by ext; simp)

/-- By `infer_instance` for `Algebra.QuasiFiniteAt R p`. -/
/-
**Algebra.WeaklyQuasiFiniteAt.finite_residueField** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebra.WeaklyQuasiFiniteAt`。
形式化陈述：finite_residueField [p.IsPrime] [q.LiesOver p] [WeaklyQuasiFiniteAt R q] [
Algebra (Localization.AtPrime p) (Localization.AtPrime q)] [Localization.AtPrime
.IsLiesOverAlgebra p q] : Module.Finite p.ResidueField q.ResidueField
参数：Localization.AtPrime p；Localization.AtPrime q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.Quotient.instIsPrimeQuotientMapRingHomAlgebraMapMkOfLiesOver`：∀ (R
 : Type u_2) [inst : CommSemiring R] {A : Type u_3} [inst_1 : CommRing A] [inst_
2 : Algebra R A] (p : Ideal R)   (P : Ideal A) [P.IsPrim…
· 使用定理 `Ideal.LiesOver.trans`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type
 u_3} [inst_1 : CommSemiring B] {C : Type u_4} [inst_2 : Semiring C]   [inst_3 :
 Algebra A…
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Finite.of_injective`：∀ {R : Type u_1} {S : Type u_2} {M : Type u_
3} {N : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommM
onoid M] [inst_3…
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Algebra.instFiniteResidueFieldOfQuasiFiniteAt`：∀ {R : Type u_1} {S : Typ
e u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ide
al R)   [inst_3 : p.IsPrime] (P : I…
· 使用定理 `IsLocalRing.ResidueField.instIsScalarTower_1`：∀ {R : Type u_1} {S : Type
 u_2} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : CommRing S]   [inst
_3 : IsLocalRing S] [inst_4 : Alge…
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra_1`：∀ {A : Type
 u_4} {B : Type u_5} {C : Type u_6} [inst : CommSemiring A] [inst_1 : CommSemiri
ng B] [inst_2 : Algebra A B]   [inst_3 : CommSemi…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
By `infer_instance` for `Algebra.QuasiFiniteAt R p`.
-/
lemma finite_residueField
    [p.IsPrime] [q.LiesOver p] [WeaklyQuasiFiniteAt R q]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Module.Finite p.ResidueField q.ResidueField := by
  let r := q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))
  have : r.LiesOver q :=
    ⟨.trans (by simp [← RingHom.ker_eq_comap_bot, Ideal.map_comap_le])
    (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver q r
  have : r.LiesOver p := .trans _ q _
  let := Localization.AtPrime.algebraOfLiesOver p r
  exact .of_injective (IsScalarTower.toAlgHom _ _ r.ResidueField).toLinearMap (RingHom.injective _)

/-- By `infer_instance` for `Algebra.QuasiFiniteAt R p`. -/
/-
**Algebra.WeaklyQuasiFiniteAt.finite_locoalization** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebra.WeaklyQuasiFiniteAt`。
形式化陈述：finite_locoalization {K : Type*} [Field K] [Algebra K S] [WeaklyQuasiFinit
eAt K q] : Module.Finite K (Localization.AtPrime q)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.QuasiFinite.of_surjective_algHom`：of_surjective_algHom [QuasiFin
ite R S] (f : S ->ₐ[R] T) (hf : Function.Surjective f) : QuasiFinite R T
· 使用定理 `Ideal.instIsTwoSidedBot`：∀ {α : Type u} [inst : Semiring α], ⊥.IsTwoSide
d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_bot`：map_bot : (⊥ : Ideal R).map f = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ideal.instLiesOverBotOfIsPrime`：∀ {K : Type u_2} {A : Type u_3} [inst : 
Field K] [inst_1 : Semiring A] [inst_2 : Algebra K A] (P : Ideal A) [P.IsPrime],
   P.LiesOver ⊥
· 使用引理 `Algebra.weaklyQuasiFiniteAt_iff`：Algebra.weaklyQuasiFiniteAt_iff : Algeb
ra.WeaklyQuasiFiniteAt R q ↔ Algebra.QuasiFinite R (Localization.AtPrime q ⧸ (q.
under R).map (algebra…
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `Module.Finite.of_quasiFinite`：∀ {R : Type u_1} {S : Type u_2} [inst : Co
mmRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [IsArtinianRing R]   [Alg
ebra.QuasiFinite R…
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R

--- 原说明 ---
By `infer_instance` for `Algebra.QuasiFiniteAt R p`.
-/
lemma finite_locoalization {K : Type*} [Field K] [Algebra K S] [WeaklyQuasiFiniteAt K q] :
    Module.Finite K (Localization.AtPrime q) := by
  have H : Algebra.WeaklyQuasiFiniteAt K q := ‹_›
  rw [Algebra.weaklyQuasiFiniteAt_iff, ← Ideal.over_def q ⊥, Ideal.map_bot] at H
  have : QuasiFinite K (Localization.AtPrime q) := .of_surjective_algHom
    (AlgEquiv.quotientBot K _).toAlgHom (AlgEquiv.quotientBot K _).surjective
  exact .of_quasiFinite

/-- Use `Algebra.QuasiFiniteAt.eq_of_le_of_under_eq` instead for `Algebra.QuasiFiniteAt R p`. -/
/-
**Algebra.WeaklyQuasiFiniteAt.eq_of_le_of_under_eq** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebra.WeaklyQuasiFiniteAt`。
形式化陈述：eq_of_le_of_under_eq {P Q : Ideal S} [P.IsPrime] [Q.IsPrime] (h₁ : P <= Q)
 (h₂ : P.under R = Q.under R) [WeaklyQuasiFiniteAt R Q] : P = Q
参数：h₁ : P <= Q；h₂ : P.under R = Q.under R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.map_isPrime_of_surjective`：map_isPrime_of_surjective {f : F} (hf :
 Function.Surjective f) {I : Ideal R} [H : IsPrime I] (hk : RingHom.ker f <= I) 
: IsPrime (map f I)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_comap_le`：map_comap_le : (K.comap f).map f <= K
· 使用定理 `Algebra.QuasiFiniteAt.eq_of_le_of_under_eq`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P Q : Idea
l S}   [P.IsPrime] [inst_4 : Q.I…
· 使用定理 `Ideal.Quotient.instIsPrimeQuotientMapRingHomAlgebraMapMkOfLiesOver`：∀ (R
 : Type u_2) [inst : CommSemiring R] {A : Type u_3} [inst_1 : CommRing A] [inst_
2 : Algebra R A] (p : Ideal R)   (P : Ideal A) [P.IsPrim…
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `Ideal.under_under`：under_under : (𝔓.under B).under A = 𝔓.under A
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用引理 `Ideal.comap_map_quotientMk`：comap_map_quotientMk (I J : Ideal R) [I.IsTw
oSided] : (J.map <| Ideal.Quotient.mk I).comap (Ideal.Quotient.mk I) = I ⊔ J
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a

--- 原说明 ---
Use `Algebra.QuasiFiniteAt.eq_of_le_of_under_eq` instead for `Algebra.QuasiFinit
eAt R p`.
-/
lemma eq_of_le_of_under_eq {P Q : Ideal S} [P.IsPrime] [Q.IsPrime]
    (h₁ : P ≤ Q) (h₂ : P.under R = Q.under R) [WeaklyQuasiFiniteAt R Q] :
    P = Q := by
  have : (P.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa [← h₂] using Ideal.map_comap_le)
  have := QuasiFiniteAt.eq_of_le_of_under_eq (R := R)
    (P := P.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S))))
    (Q := Q.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S))))
    (Ideal.map_mono h₁) (by
      rw [← Ideal.under_under (B := S), ← Ideal.under_under (A := R) (B := S) (C := S ⧸ _)]
      dsimp [Ideal.under] at h₂ ⊢
      simp [Ideal.map_comap_le]
      simp [Ideal.map_comap_le, ← h₂])
  replace this := (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm.trans
    congr($(this).comap _)
  simp [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.map_comap_le] at this
  simpa [Ideal.map_comap_le, ← h₂] using this

open _root_.TensorProduct in
/-- Use `Algebra.QuasiFiniteAt.baseChange` instead for `Algebra.QuasiFiniteAt R p`. -/
/-
**Algebra.WeaklyQuasiFiniteAt.baseChange** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Weak
lyQuasiFiniteAt`。
形式化陈述：baseChange (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p] {A : Type*}
 [CommRing A] [Algebra R A] (q : Ideal (A otimes[R] S)) [q.IsPrime] (hq : p = q.
comap TensorProduct.includeRight.toRingHom) : WeaklyQuasiFiniteAt A q
参数：p : Ideal S；q : Ideal (A otimes[R] S)；hq : p = q.comap TensorProduct.includeR
ight.toRingHom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.TensorProduct.map_surjective`：Algebra.TensorProduct.map_surjecti
ve (hf : Function.Surjective f) (hg : Function.Surjective g) : Function.Surjecti
ve (map f g)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Algebra.TensorProduct.map_ker`：Algebra.TensorProduct.map_ker (hf : Funct
ion.Surjective f) (hg : Function.Surjective g) : RingHom.ker (map f g) = (RingHo
m.ker f).map (Algeb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.ker_coe_toRingHom`：ker_coe_toRingHom : ker (f : R ->+* S) = ker 
f
· 使用引理 `Ideal.map_coe`：map_coe [RingHomClass F R S] (I : Ideal R) : I.map (f : R
 ->+* S) = I.map f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.Quotient.mkₐ_ker`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : CommSem
iring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst_3 : I.
IsTwoSided],…
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `Ideal.map_comap_le`：map_comap_le : (K.comap f).map f <= K
· 使用定理 `Ideal.map_isPrime_of_surjective`：map_isPrime_of_surjective {f : F} (hf :
 Function.Surjective f) {I : Ideal R} [H : IsPrime I] (hk : RingHom.ker f <= I) 
: IsPrime (map f I)
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Algebra.QuasiFiniteAt.baseChange`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal S)   [inst
_3 : p.IsPrime] [Algeb…
· 使用定理 `Ideal.Quotient.instIsPrimeQuotientMapRingHomAlgebraMapMkOfLiesOver`：∀ (R
 : Type u_2) [inst : CommSemiring R] {A : Type u_3} [inst_1 : CommRing A] [inst_
2 : Algebra R A] (p : Ideal R)   (P : Ideal A) [P.IsPrim…
· 使用定理 `Ideal.comap_injective_of_surjective`：comap_injective_of_surjective : Inj
ective (comap f)
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Use `Algebra.QuasiFiniteAt.baseChange` instead for `Algebra.QuasiFiniteAt R p`.
-/
lemma baseChange (p : Ideal S) [p.IsPrime] [WeaklyQuasiFiniteAt R p]
    {A : Type*} [CommRing A] [Algebra R A] (q : Ideal (A ⊗[R] S)) [q.IsPrime]
    (hq : p = q.comap TensorProduct.includeRight.toRingHom) :
    WeaklyQuasiFiniteAt A q := by
  delta WeaklyQuasiFiniteAt at *
  let φ : A ⊗[R] S →ₐ[A] (A ⧸ q.under A) ⊗[R] (S ⧸ (p.under R).map (algebraMap R S)) :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ _ _) (Ideal.Quotient.mkₐ _ _)
  have hφ₁ : Function.Surjective φ :=
    Algebra.TensorProduct.map_surjective _ _
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective
  have hφ₂ : RingHom.ker φ.toRingHom = (q.under A).map (algebraMap _ _) := by
    refine (Algebra.TensorProduct.map_ker _ _
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective).trans ?_
    rw [← RingHom.ker_coe_toRingHom, ← RingHom.ker_coe_toRingHom (F := AlgHom _ _ _),
      ← Ideal.map_coe, ← Ideal.map_coe (F := AlgHom _ _ _)]
    simp only [Ideal.under, Ideal.Quotient.mkₐ_ker, hq, AlgHom.toRingHom_eq_coe, Ideal.comap_comap,
      AlgHom.comp_algebraMap_of_tower, Ideal.map_map]
    refine sup_eq_left.mpr ?_
    simp only [← TensorProduct.includeLeft.comp_algebraMap, ← Ideal.map_map, ← Ideal.comap_comap]
    exact Ideal.map_mono Ideal.map_comap_le
  have hφ₃ : φ.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (Ideal.Quotient.mk _) := rfl
  have : (Ideal.map φ.toRingHom q).IsPrime :=
    Ideal.map_isPrime_of_surjective ‹_› <| hφ₂.trans_le Ideal.map_comap_le
  have := QuasiFiniteAt.baseChange (R := R) (S := _) (A := A ⧸ q.under A)
    (p.map (Ideal.Quotient.mk ((p.under R).map (algebraMap R S)))) (q.map φ.toRingHom) (by
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_comap,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr Ideal.map_comap_le,
      ← hφ₃, ← Ideal.comap_comap, Ideal.comap_map_of_surjective _ (by exact hφ₁),
      ← RingHom.ker_eq_comap_bot, hφ₂, sup_eq_left.mpr Ideal.map_comap_le])
  have : QuasiFiniteAt A (q.map φ.toRingHom) := .trans _ (A ⧸ q.under A) _
  let e := (Ideal.quotientEquivAlg ((q.under A).map (algebraMap _ _)) _ (.refl) (by simpa)).trans
    (Ideal.quotientKerAlgEquivOfSurjective hφ₁)
  refine .of_surjectiveOnStalks (q.map φ.toRingHom) e.symm.toAlgHom
    e.symm.toRingEquiv.surjectiveOnStalks _ ?_
  erw [Ideal.comap_symm] -- This should be fixed once `Ideal.map` does not take homclasses.
  rw [← Ideal.map_coe e.toRingEquiv, Ideal.map_map]
  rfl

open _root_.TensorProduct in
variable (R S) in
/-- Use `Algebra.QuasiFinite.of_restrictScalars` instead for `Algebra.QuasiFiniteAt R p`. -/
/-
**Algebra.WeaklyQuasiFiniteAt.of_restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 `Alge
bra.WeaklyQuasiFiniteAt`。
形式化陈述：of_restrictScalars [Algebra S T] [IsScalarTower R S T] (q : Ideal T) [q.Is
Prime] [WeaklyQuasiFiniteAt R q] : WeaklyQuasiFiniteAt S q
参数：q : Ideal T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.instIsPrimeQuotientMapRingHomAlgebraMapMkOfLiesOver`：∀ (R
 : Type u_2) [inst : CommSemiring R] {A : Type u_3} [inst_1 : CommRing A] [inst_
2 : Algebra R A] (p : Ideal R)   (P : Ideal A) [P.IsPrim…
· 使用引理 `Algebra.QuasiFinite.of_restrictScalars`：of_restrictScalars [QuasiFinite 
R T] : QuasiFinite S T
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `Ideal.map_comap_le`：map_comap_le : (K.comap f).map f <= K
· 使用定理 `Algebra.QuasiFiniteAt.of_surjectiveOnStalks`：∀ {R : Type u_1} {S : Type 
u_2} {T : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing
 T]   [inst_3 : Algebra R S] [ins…
· 使用引理 `RingHom.surjectiveOnStalks_of_surjective`：surjectiveOnStalks_of_surjecti
ve (h : Function.Surjective f) : SurjectiveOnStalks f
· 使用定理 `Ideal.quotientMap_surjective`：quotientMap_surjective {J : Ideal R} {I : 
Ideal S} [I.IsTwoSided] [J.IsTwoSided] {f : R ->+* S} {H : J <= I.comap f} (hf :
 Function.Surjecti…
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用定理 `Ideal.comap_injective_of_surjective`：comap_injective_of_surjective : Inj
ective (comap f)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Use `Algebra.QuasiFinite.of_restrictScalars` instead for `Algebra.QuasiFiniteAt 
R p`.
-/
lemma of_restrictScalars [Algebra S T] [IsScalarTower R S T]
    (q : Ideal T) [q.IsPrime] [WeaklyQuasiFiniteAt R q] :
    WeaklyQuasiFiniteAt S q := by
  have : Algebra.QuasiFiniteAt S (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R T)))) :=
    .of_restrictScalars R _ _
  have H : (q.under R).map (algebraMap R T) ≤ (q.under S).map (algebraMap S T) := by
    simpa [Ideal.under, IsScalarTower.algebraMap_eq R S T, ← Ideal.map_map,
      ← Ideal.comap_comap, -Ideal.under_under] using Ideal.map_mono Ideal.map_comap_le
  delta WeaklyQuasiFiniteAt
  refine .of_surjectiveOnStalks (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R T))))
    (Ideal.quotientMapₐ _ (.id _ _) (by exact H)) (RingHom.surjectiveOnStalks_of_surjective
      (Ideal.quotientMap_surjective (H := by exact H) Function.surjective_id)) _ ?_
  apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  rw [Ideal.comap_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  refine .trans ?_ (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm
  simp [← RingHom.ker_eq_comap_bot, Ideal.map_comap_le]

/-- Use `Algebra.QuasiFinite.of_quasiFiniteAt_residueField` instead
for `Algebra.QuasiFiniteAt R q`. -/
/-
**Algebra.WeaklyQuasiFiniteAt.of_quasiFiniteAt_residueField** 是 Mathlib 中的一个引理，位
于命名空间 `Algebra.WeaklyQuasiFiniteAt`。
形式化陈述：of_quasiFiniteAt_residueField [p.IsPrime] [q.LiesOver p] (Q : Ideal (p.Fib
er S)) [Q.IsPrime] (hQ : Q.comap Algebra.TensorProduct.includeRight.toRingHom = 
q) [Algebra.QuasiFiniteAt p.ResidueField Q] : Algebra.WeaklyQuasiFiniteAt R q
参数：Q : Ideal (p.Fiber S)；hQ : Q.comap Algebra.TensorProduct.includeRight.toRingH
om = q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.weaklyQuasiFiniteAt_iff`：Algebra.weaklyQuasiFiniteAt_iff : Algeb
ra.WeaklyQuasiFiniteAt R q ↔ Algebra.QuasiFinite R (Localization.AtPrime q ⧸ (q.
under R).map (algebra…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.AtPrime.map_eq_maximalIdeal`：map_eq_maximalIdeal : p.map 
(algebraMap R Rₚ) = maximalIdeal Rₚ
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用引理 `Ideal.comap_coe`：comap_coe [RingHomClass F R S] (I : Ideal S) : I.comap 
(f : R ->+* S) = I.comap f
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.coe_toAlgHom`：coe_toAlgHom : ↑(toAlgHom R S A) = algebraMa
p S A
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Ideal.Fiber.exists_smul_eq_one_tmul`：∀ {R : Type u_1} {S : Type u_2} [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   [i
nst_3 : p.IsPrime] (x : p…
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ideal.instLiesOverFiberOfIsPrime`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   [inst
_3 : p.IsPrime] (q : I…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
Use `Algebra.QuasiFinite.of_quasiFiniteAt_residueField` instead
for `Algebra.QuasiFiniteAt R q`.
-/
lemma of_quasiFiniteAt_residueField [p.IsPrime] [q.LiesOver p]
    (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    (hQ : Q.comap Algebra.TensorProduct.includeRight.toRingHom = q)
    [Algebra.QuasiFiniteAt p.ResidueField Q] :
    Algebra.WeaklyQuasiFiniteAt R q := by
  rw [Algebra.weaklyQuasiFiniteAt_iff]
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let φ₁ : p.ResidueField →ₐ[R] Sq ⧸ p.map (algebraMap R Sq) :=
    Ideal.quotientMapₐ _ (IsScalarTower.toAlgHom _ _ _) (by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p, Ideal.map_le_iff_le_comap,
      ← Ideal.comap_coe (F := AlgHom _ _ _), Ideal.comap_comap]
    simpa [← IsScalarTower.algebraMap_eq] using Ideal.le_comap_map)
  let φ₂ : p.Fiber S →ₐ[R] Sq ⧸ p.map (algebraMap R Sq) :=
    Algebra.TensorProduct.lift φ₁ (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _
  let φ₃ : Localization.AtPrime Q →ₐ[R] Sq ⧸ p.map (algebraMap R Sq) :=
    IsLocalization.liftAlgHom (M := Q.primeCompl) (f := φ₂) <| by
      rintro ⟨y, hy⟩
      obtain ⟨r, hrp, s, H⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ y
      suffices IsUnit (φ₂ (1 ⊗ₜ s)) by
        rw [← H, map_smul, Algebra.smul_def, IsUnit.mul_iff] at this
        exact this.2
      suffices s ∉ q by
        have := (IsLocalization.map_units (M := q.primeCompl) Sq ⟨_, this⟩).map
          (algebraMap _ (Sq ⧸ p.map (algebraMap R Sq)))
        simpa [φ₂, ← IsScalarTower.algebraMap_apply] using this
      suffices algebraMap _ _ r * y ∉ Q by simpa [← hQ, ← H, Algebra.smul_def]
      refine Q.primeCompl.mul_mem ?_ hy
      simpa only [Ideal.mem_primeCompl_iff, ← Ideal.mem_comap, ← Q.over_def p]
  have : Function.Surjective φ₃ := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
    refine ⟨IsLocalization.mk' (M := Q.primeCompl) _ (1 ⊗ₜ x) ⟨1 ⊗ₜ s, ?_⟩, ?_⟩
    · simpa [← hQ] using hs
    · simp [φ₃, IsLocalization.lift_mk'_spec, φ₂, IsScalarTower.algebraMap_apply S Sq (Sq ⧸ _),
        -Ideal.Quotient.mk_algebraMap, ← map_mul]
  have inst : QuasiFiniteAt R Q := .trans _ p.ResidueField _
  obtain rfl := q.over_def p
  exact .of_surjective_algHom φ₃ this

end Algebra.WeaklyQuasiFiniteAt

