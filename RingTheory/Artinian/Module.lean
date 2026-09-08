/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.Regular.Opposite
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Jacobson.Semiprimary
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Artinian rings and modules

A module satisfying these equivalent conditions is said to be an *Artinian* R-module
if every decreasing chain of submodules is eventually constant, or equivalently,
if the relation `<` on submodules is well founded.

A ring is said to be left (or right) Artinian if it is Artinian as a left (or right) module over
itself, or simply Artinian if it is both left and right Artinian.

## Main results

* `IsArtinianRing.primeSpectrum_finite`, `IsArtinianRing.isMaximal_of_isPrime`: there are only
  finitely prime ideals in a commutative Artinian ring, and each of them is maximal.

* `IsArtinianRing.equivPi`: a reduced commutative Artinian ring `R` is isomorphic to a finite
  product of fields (and therefore is a semisimple ring and a decomposition monoid; moreover
  `R[X]` is also a decomposition monoid).

* `IsArtinian.isSemisimpleModule_iff_jacobson`: an Artinian module is semisimple
  iff its Jacobson radical is zero.

* `instIsSemiprimaryRingOfIsArtinianRing`: an Artinian ring `R` is semiprimary, in particular
  the Jacobson radical of `R` is a nilpotent ideal (`IsArtinianRing.isNilpotent_jacobson_bot`).

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Artinian, artinian, Artinian ring, Artinian module, artinian ring, artinian module

-/

@[expose] public section

open Set Filter Pointwise

section Semiring

variable {R M P N : Type*}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid P] [AddCommMonoid N]
variable [Module R M] [Module R P] [Module R N]

/-
**LinearMap.isArtinian_iff_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.isArtinian_iff_of_bijective {S P} [Semiring S] [AddCommMonoid P]
 [Module S P] {σ : R ->+* S} [RingHomSurjective σ] (l : M ->ₛₗ[σ] P) (hl : Funct
ion.Bijective l) : IsArtinian R M ↔ IsArtinian S P
参数：l : M ->ₛₗ[σ] P；hl : Function.Bijective l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.wellFoundedLT`：StrictMono.wellFoundedLT [WellFoundedLT β] (hf
 : StrictMono f) : WellFoundedLT α
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
theorem LinearMap.isArtinian_iff_of_bijective {S P} [Semiring S] [AddCommMonoid P] [Module S P]
    {σ : R →+* S} [RingHomSurjective σ] (l : M →ₛₗ[σ] P) (hl : Function.Bijective l) :
    IsArtinian R M ↔ IsArtinian S P :=
  let e := Submodule.orderIsoMapComapOfBijective l hl
  ⟨fun _ ↦ e.symm.strictMono.wellFoundedLT, fun _ ↦ e.strictMono.wellFoundedLT⟩
/-
**isArtinian_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isArtinian_of_injective (f : M ->ₗ[R] P) (h : Function.Injective f) [IsArt
inian R P] : IsArtinian R M
参数：f : M ->ₗ[R] P；h : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.wf`：∀ {α : Sort u} {r q : α → α → Prop}, Subrelation q r → W
ellFounded r → WellFounded q
· 使用定理 `Submodule.map_strictMono_of_injective`：map_strictMono_of_injective : Str
ictMono (map f)
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
theorem isArtinian_of_injective (f : M →ₗ[R] P) (h : Function.Injective f) [IsArtinian R P] :
    IsArtinian R M :=
  ⟨Subrelation.wf
    (fun {A B} hAB => show A.map f < B.map f from Submodule.map_strictMono_of_injective h hAB)
    (InvImage.wf (Submodule.map f) IsWellFounded.wf)⟩
/-
**isArtinian_submodule'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isArtinian_submodule' [IsArtinian R M] (N : Submodule R M) : IsArtinian R 
N
参数：N : Submodule R M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isArtinian_of_injective`：isArtinian_of_injective (f : M ->ₗ[R] P) (h : F
unction.Injective f) [IsArtinian R P] : IsArtinian R M
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
instance isArtinian_submodule' [IsArtinian R M] (N : Submodule R M) : IsArtinian R N :=
  isArtinian_of_injective N.subtype Subtype.val_injective
/-
**isArtinian_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isArtinian_of_le {s t : Submodule R M} [IsArtinian R t] (h : s <= t) : IsA
rtinian R s
参数：h : s <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isArtinian_of_injective`：isArtinian_of_injective (f : M ->ₗ[R] P) (h : F
unction.Injective f) [IsArtinian R P] : IsArtinian R M
· 使用定理 `Submodule.inclusion_injective`：inclusion_injective (h : p <= p') : Funct
ion.Injective (inclusion h)
-/
theorem isArtinian_of_le {s t : Submodule R M} [IsArtinian R t] (h : s ≤ t) : IsArtinian R s :=
  isArtinian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

variable (M) in
/-
**isArtinian_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isArtinian_of_surjective (f : M ->ₗ[R] P) (hf : Function.Surjective f) [Is
Artinian R M] : IsArtinian R P
参数：f : M ->ₗ[R] P；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.wf`：∀ {α : Sort u} {r q : α → α → Prop}, Subrelation q r → W
ellFounded r → WellFounded q
· 使用定理 `Submodule.comap_strictMono_of_surjective`：comap_strictMono_of_surjective
 : StrictMono (comap f)
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
theorem isArtinian_of_surjective (f : M →ₗ[R] P) (hf : Function.Surjective f) [IsArtinian R M] :
    IsArtinian R P :=
  ⟨Subrelation.wf
    (fun {A B} hAB =>
      show A.comap f < B.comap f from Submodule.comap_strictMono_of_surjective hf hAB)
    (InvImage.wf (Submodule.comap f) IsWellFounded.wf)⟩

/--
If `M` is an Artinian `R` module, and `S` is an `R`-algebra with a surjective
algebra map, then `M` is an Artinian `S` module.
-/
/-
**isArtinian_of_surjective_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isArtinian_of_surjective_algebraMap {S : Type*} [CommSemiring S] [Algebra 
S R] [Module S M] [IsArtinian R M] [IsScalarTower S R M] (H : Function.Surjectiv
e (algebraMap S R)) : IsArtinian S M
参数：H : Function.Surjective (algebraMap S R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.wellFoundedLT`：∀ {α : Type u_2} {β : Type u_3} [inst : Pr
eorder α] [inst_1 : Preorder β] [WellFoundedLT β] (f : α ↪o β),   WellFoundedLT 
α
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Submodule.ext_iff`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {p q : Submodule R M}, p = 
q ↔ ∀ (…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `M` is an Artinian `R` module, and `S` is an `R`-algebra with a surjective
algebra map, then `M` is an Artinian `S` module.
-/
theorem isArtinian_of_surjective_algebraMap {S : Type*} [CommSemiring S] [Algebra S R]
    [Module S M] [IsArtinian R M] [IsScalarTower S R M]
    (H : Function.Surjective (algebraMap S R)) : IsArtinian S M := by
  apply (OrderEmbedding.wellFoundedLT (β := Submodule R M))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro N
    refine { toAddSubmonoid := N.toAddSubmonoid, smul_mem' := ?_ }
    intro c x hx
    obtain ⟨r, rfl⟩ := H c
    suffices r • x ∈ N by simpa [Algebra.algebraMap_eq_smul_one, smul_assoc]
    apply N.smul_mem _ hx
  · intro N1 N2 h
    rwa [Submodule.ext_iff] at h ⊢
  · intro N1 N2
    rfl
/-
**isArtinian_range** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isArtinian_range (f : M ->ₗ[R] P) [IsArtinian R M] : IsArtinian R (LinearM
ap.range f)
参数：f : M ->ₗ[R] P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isArtinian_of_surjective`：isArtinian_of_surjective (f : M ->ₗ[R] P) (hf 
: Function.Surjective f) [IsArtinian R M] : IsArtinian R P
· 使用定理 `LinearMap.surjective_rangeRestrict`：surjective_rangeRestrict : Surjectiv
e f.rangeRestrict
-/
instance isArtinian_range (f : M →ₗ[R] P) [IsArtinian R M] : IsArtinian R (LinearMap.range f) :=
  isArtinian_of_surjective _ _ f.surjective_rangeRestrict
/-
**isArtinian_of_linearEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isArtinian_of_linearEquiv (f : M ≃ₗ[R] P) [IsArtinian R M] : IsArtinian R 
P
参数：f : M ≃ₗ[R] P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isArtinian_of_surjective`：isArtinian_of_surjective (f : M ->ₗ[R] P) (hf 
: Function.Surjective f) [IsArtinian R M] : IsArtinian R P
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem isArtinian_of_linearEquiv (f : M ≃ₗ[R] P) [IsArtinian R M] : IsArtinian R P :=
  isArtinian_of_surjective _ f.toLinearMap f.toEquiv.surjective
/-
**LinearEquiv.isArtinian_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.isArtinian_iff (f : M ≃ₗ[R] P) : IsArtinian R M ↔ IsArtinian R
 P
参数：f : M ≃ₗ[R] P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isArtinian_of_linearEquiv`：isArtinian_of_linearEquiv (f : M ≃ₗ[R] P) [Is
Artinian R M] : IsArtinian R P
-/
theorem LinearEquiv.isArtinian_iff (f : M ≃ₗ[R] P) : IsArtinian R M ↔ IsArtinian R P :=
  ⟨fun _ ↦ isArtinian_of_linearEquiv f, fun _ ↦ isArtinian_of_linearEquiv f.symm⟩

-- This was previously a global instance,
-- but it doesn't appear to be used and has been implicated in slow typeclass resolutions.
/-
**isArtinian_of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isArtinian_of_finite [Finite M] : IsArtinian R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.wellFounded_of_trans_of_irrefl`：wellFounded_of_trans_of_irrefl (r
 : α -> α -> Prop) [IsTrans α r] [Std.Irrefl r] : WellFounded r
· 使用定理 `SetLike.instFinite`：∀ {A : Type u_1} {B : Type u_2} [SetLike A B] [Finit
e B], Finite A
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
lemma isArtinian_of_finite [Finite M] : IsArtinian R M :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

open Submodule
/-
**IsArtinian.finite_of_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsArtinian.finite_of_linearIndependent [Nontrivial R] [h : IsArtinian R M]
 {s : Set M} (hs : LinearIndependent R ((↑) : s -> M)) : s.Finite
参数：hs : LinearIndependent R ((↑) : s -> M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedLT.finite_of_iSupIndep`：WellFoundedLT.finite_of_iSupIndep [We
llFoundedLT α] {ι : Type*} {t : ι -> α} (ht : iSupIndep t) (h_ne_bot : forall i,
 t i != ⊥) : Finite ι
· 使用定理 `LinearIndependent.iSupIndep_span_singleton`：LinearIndependent.iSupIndep_
span_singleton (hv : LinearIndependent R v) : iSupIndep fun i => R ∙ v i
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsArtinian.finite_of_linearIndependent [Nontrivial R] [h : IsArtinian R M] {s : Set M}
    (hs : LinearIndependent R ((↑) : s → M)) : s.Finite :=
  WellFoundedLT.finite_of_iSupIndep hs.iSupIndep_span_singleton fun i _ ↦ hs.ne_zero i (by simp_all)

/-- A module is Artinian iff every nonempty set of submodules has a minimal submodule among them. -/
/-
**set_has_minimal_iff_artinian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：set_has_minimal_iff_artinian : (forall a : Set <| Submodule R M, a.Nonempt
y -> exists M' in a, forall I in a, ¬I < M') ↔ IsArtinian R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isArtinian_iff`：isArtinian_iff (R M) [Semiring R] [AddCommMonoid M] [Mod
ule R M] : IsArtinian R M ↔ WellFounded (· < · : Submodule R M -> Submodule R M 
-> P…
· 使用定理 `WellFounded.wellFounded_iff_has_min`：wellFounded_iff_has_min {r : α -> α
 -> Prop} : WellFounded r ↔ forall s : Set α, s.Nonempty -> exists m in s, foral
l x in s, ¬r x m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A module is Artinian iff every nonempty set of submodules has a minimal submodul
e among them.
-/
theorem set_has_minimal_iff_artinian :
    (∀ a : Set <| Submodule R M, a.Nonempty → ∃ M' ∈ a, ∀ I ∈ a, ¬I < M') ↔ IsArtinian R M := by
  rw [isArtinian_iff, WellFounded.wellFounded_iff_has_min]
/-
**IsArtinian.set_has_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsArtinian.set_has_minimal [IsArtinian R M] (a : Set <| Submodule R M) (ha
 : a.Nonempty) : exists M' in a, forall I in a, ¬I < M'
参数：a : Set <| Submodule R M；ha : a.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `set_has_minimal_iff_artinian`：set_has_minimal_iff_artinian : (forall a :
 Set <| Submodule R M, a.Nonempty -> exists M' in a, forall I in a, ¬I < M') ↔ I
sArtinian R M
-/
theorem IsArtinian.set_has_minimal [IsArtinian R M] (a : Set <| Submodule R M) (ha : a.Nonempty) :
    ∃ M' ∈ a, ∀ I ∈ a, ¬I < M' :=
  set_has_minimal_iff_artinian.mpr ‹_› a ha

/-- A module is Artinian iff every decreasing chain of submodules stabilizes. -/
/-
**monotone_stabilizes_iff_artinian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_stabilizes_iff_artinian : (forall f : Nat ->o (Submodule R M)ᵒᵈ, 
exists n, forall m, n <= m -> f n = f m) ↔ IsArtinian R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `wellFoundedGT_iff_monotone_chain_condition`：wellFoundedGT_iff_monotone_c
hain_condition [PartialOrder α] : WellFoundedGT α ↔ forall a : Nat ->o α, exists
 n, forall m, n <= m -> a n = a …

--- 原说明 ---
A module is Artinian iff every decreasing chain of submodules stabilizes.
-/
theorem monotone_stabilizes_iff_artinian :
    (∀ f : ℕ →o (Submodule R M)ᵒᵈ, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsArtinian R M :=
  wellFoundedGT_iff_monotone_chain_condition.symm

namespace IsArtinian

variable [IsArtinian R M]

/-
**IsArtinian.monotone_stabilizes** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinian`。
形式化陈述：monotone_stabilizes (f : Nat ->o (Submodule R M)ᵒᵈ) : exists n, forall m, 
n <= m -> f n = f m
参数：f : Nat ->o (Submodule R M)ᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotone_stabilizes_iff_artinian`：monotone_stabilizes_iff_artinian : (fo
rall f : Nat ->o (Submodule R M)ᵒᵈ, exists n, forall m, n <= m -> f n = f m) ↔ I
sArtinian R M
-/
theorem monotone_stabilizes (f : ℕ →o (Submodule R M)ᵒᵈ) : ∃ n, ∀ m, n ≤ m → f n = f m :=
  monotone_stabilizes_iff_artinian.mpr ‹_› f
/-
**IsArtinian.eventuallyConst_of_isArtinian** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinian
`。
形式化陈述：eventuallyConst_of_isArtinian (f : Nat ->o (Submodule R M)ᵒᵈ) : atTop.Even
tuallyConst f
参数：f : Nat ->o (Submodule R M)ᵒᵈ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsArtinian.monotone_stabilizes`：monotone_stabilizes (f : Nat ->o (Submod
ule R M)ᵒᵈ) : exists n, forall m, n <= m -> f n = f m
-/
theorem eventuallyConst_of_isArtinian (f : ℕ →o (Submodule R M)ᵒᵈ) :
    atTop.EventuallyConst f := by
  simp_rw [eventuallyConst_atTop, eq_comm]
  exact monotone_stabilizes f

open Function

/-- Any injective endomorphism of an Artinian module is surjective. -/
/-
**IsArtinian.surjective_of_injective_endomorphism** 是 Mathlib 中的一个定理，位于命名空间 `IsA
rtinian`。
形式化陈述：surjective_of_injective_endomorphism (f : M ->ₗ[R] M) (s : Injective f) : 
Surjective f
参数：f : M ->ₗ[R] M；s : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsArtinian.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   IsArtinian R M = WellFou
ndedL…
· 使用定理 `WellFoundedLT.eq_1`：∀ (α : Type u_1) [inst : LT α], WellFoundedLT α = Is
WellFounded α fun x1 x2 => x1 < x2
· 使用定理 `isWellFounded_iff`：∀ (α : Type u) (r : α → α → Prop), IsWellFounded α r 
↔ WellFounded r
· 使用定理 `RelEmbedding.not_wellFounded`：not_wellFounded (f : ((· > ·) : Nat -> Nat
 -> Prop) ↪r r) : ¬WellFounded r
· 使用定理 `instIsStrictOrderLt`：∀ {α : Type u} [inst : Preorder α], IsStrictOrder α
 fun x1 x2 => x1 < x2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.range.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u
_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCo
mmMonoid M] [ins…
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.map_strictMono_of_injective`：map_strictMono_of_injective : Str
ictMono (map f)
· 使用定理 `Module.End.iterate_injective`：∀ {R : Type u_1} {M : Type u_4} [inst : Se
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {f' : Module
.End R M}, Functio…
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f

--- 原说明 ---
Any injective endomorphism of an Artinian module is surjective.
-/
theorem surjective_of_injective_endomorphism (f : M →ₗ[R] M) (s : Injective f) : Surjective f := by
  have h := ‹IsArtinian R M›; contrapose h
  rw [IsArtinian, WellFoundedLT, isWellFounded_iff]
  refine (RelEmbedding.natGT (LinearMap.range <| f ^ ·) ?_).not_wellFounded
  intro n
  simp_rw [pow_succ, Module.End.mul_eq_comp, LinearMap.range_comp, ← Submodule.map_top (f ^ n)]
  refine Submodule.map_strictMono_of_injective (Module.End.iterate_injective s n) (Ne.lt_top ?_)
  rwa [Ne, LinearMap.range_eq_top]

/-- Any injective endomorphism of an Artinian module is bijective. -/
/-
**IsArtinian.bijective_of_injective_endomorphism** 是 Mathlib 中的一个定理，位于命名空间 `IsAr
tinian`。
形式化陈述：bijective_of_injective_endomorphism (f : M ->ₗ[R] M) (s : Injective f) : B
ijective f
参数：f : M ->ₗ[R] M；s : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinian.surjective_of_injective_endomorphism`：surjective_of_injective
_endomorphism (f : M ->ₗ[R] M) (s : Injective f) : Surjective f

--- 原说明 ---
Any injective endomorphism of an Artinian module is bijective.
-/
theorem bijective_of_injective_endomorphism (f : M →ₗ[R] M) (s : Injective f) : Bijective f :=
  ⟨s, surjective_of_injective_endomorphism f s⟩

/-- A sequence `f` of submodules of an Artinian module,
with the supremum `f (n+1)` and the infimum of `f 0`, ..., `f n` being ⊤,
is eventually ⊤. -/
/-
**IsArtinian.disjoint_partial_infs_eventually_top** 是 Mathlib 中的一个定理，位于命名空间 `IsA
rtinian`。
形式化陈述：disjoint_partial_infs_eventually_top (f : Nat -> Submodule R M) (h : foral
l n, Disjoint (partialSups (OrderDual.toDual ∘ f) n) (OrderDual.toDual (f (n + 1
)))) : exists n : Nat, forall m, n <= m -> f m = ⊤
参数：f : Nat -> Submodule R M；h : forall n, Disjoint (partialSups (OrderDual.toDua
l ∘ f) n) (OrderDual.toDual (f (n + 1)))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinian.monotone_stabilizes`：monotone_stabilizes (f : Nat ->o (Submod
ule R M)ᵒᵈ) : exists n, forall m, n <= m -> f n = f m
· 使用定理 `Disjoint.eq_bot_of_ge`：Disjoint.eq_bot_of_ge (hab : Disjoint a b) : b <=
 a -> b = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `partialSups_add_one`：partialSups_add_one [Add ι] [One ι] [LocallyFiniteO
rderBot ι] [SuccAddOrder ι] (f : ι -> α) (i : ι) : partialSups f (i + 1) = parti
alSups f …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canon
icallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Nat.succ_le_succ_iff`：∀ {a b : ℕ}, a.succ ≤ b.succ ↔ a ≤ b

--- 原说明 ---
A sequence `f` of submodules of an Artinian module,
with the supremum `f (n+1)` and the infimum of `f 0`, ..., `f n` being ⊤,
is eventually ⊤.
-/
theorem disjoint_partial_infs_eventually_top (f : ℕ → Submodule R M)
    (h : ∀ n, Disjoint (partialSups (OrderDual.toDual ∘ f) n) (OrderDual.toDual (f (n + 1)))) :
    ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊤ := by
  -- A little off-by-one cleanup first:
  rsuffices ⟨n, w⟩ : ∃ n : ℕ, ∀ m, n ≤ m → OrderDual.toDual f (m + 1) = ⊤
  · use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact Nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes (partialSups (OrderDual.toDual ∘ f))
  refine ⟨n, fun m p ↦ (h m).eq_bot_of_ge <| sup_eq_left.mp ?_⟩
  simpa only [partialSups_add_one] using! (w (m + 1) <| le_add_right p).symm.trans <| w m p

end IsArtinian

/-
**IsArtinian.subsingleton_of_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsArtinian.subsingleton_of_injective [IsArtinian R N] {f : P × N ->ₗ[R] N}
 (inj : Function.Injective f) : Subsingleton P
参数：inj : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_forall_eq`：∀ {α : Sort u_1} (x : α), (∀ (y : α), y = x) 
→ Subsingleton α
· 使用定理 `IsArtinian.surjective_of_injective_endomorphism`：surjective_of_injective
_endomorphism (f : M ->ₗ[R] M) (s : Injective f) : Surjective f
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma IsArtinian.subsingleton_of_injective [IsArtinian R N] {f : P × N →ₗ[R] N}
    (inj : Function.Injective f) : Subsingleton P :=
  subsingleton_of_forall_eq 0 fun p ↦
    have ⟨_, eq⟩ := IsArtinian.surjective_of_injective_endomorphism (f ∘ₗ .inr ..)
      (inj.comp (Prod.mk_right_injective _)) (f (p, 0))
    congr($(inj eq).1).symm

namespace LinearMap

variable [IsArtinian R M]

/-
**LinearMap.eventually_iInf_range_pow_eq** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：eventually_iInf_range_pow_eq (f : Module.End R M) : forallᶠ n in atTop, ⨅ 
m, LinearMap.range (f ^ m) = LinearMap.range (f ^ n)
参数：f : Module.End R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinian.monotone_stabilizes`：monotone_stabilizes (f : Nat ->o (Submod
ule R M)ᵒᵈ) : exists n, forall m, n <= m -> f n = f m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma eventually_iInf_range_pow_eq (f : Module.End R M) :
    ∀ᶠ n in atTop, ⨅ m, LinearMap.range (f ^ m) = LinearMap.range (f ^ n) := by
  obtain ⟨n, hn : ∀ m, n ≤ m → LinearMap.range (f ^ n) = LinearMap.range (f ^ m)⟩ :=
    IsArtinian.monotone_stabilizes f.iterateRange
  refine eventually_atTop.mpr ⟨n, fun l hl ↦ le_antisymm (iInf_le _ _) (le_iInf fun m ↦ ?_)⟩
  rcases le_or_gt l m with h | h
  · rw [← hn _ (hl.trans h), hn _ hl]
  · exact f.iterateRange.monotone h.le

end LinearMap

end Semiring

section Ring

variable {R M P N : Type*}
variable [Ring R] [AddCommGroup M] [AddCommGroup P] [AddCommGroup N]
variable [Module R M] [Module R P] [Module R N]

/-
**isArtinian_of_quotient_of_artinian** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isArtinian_of_quotient_of_artinian (N : Submodule R M) [IsArtinian R M] : 
IsArtinian R (M ⧸ N)
参数：N : Submodule R M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isArtinian_of_surjective`：isArtinian_of_surjective (f : M ->ₗ[R] P) (hf 
: Function.Surjective f) [IsArtinian R M] : IsArtinian R P
· 使用定理 `Submodule.Quotient.mk_surjective`：mk_surjective : Function.Surjective (@
mk _ _ _ _ _ p)
-/
instance isArtinian_of_quotient_of_artinian
    (N : Submodule R M) [IsArtinian R M] : IsArtinian R (M ⧸ N) :=
  isArtinian_of_surjective M (Submodule.mkQ N) (Submodule.Quotient.mk_surjective N)
/-
**isArtinian_of_range_eq_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isArtinian_of_range_eq_ker [IsArtinian R M] [IsArtinian R P] (f : M ->ₗ[R]
 N) (g : N ->ₗ[R] P) (h : LinearMap.range f = LinearMap.ker g) : IsArtinian R N
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] P；h : LinearMap.range f = LinearMap.ker g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wellFounded_lt_exact_sequence`：wellFounded_lt_exact_sequence {β γ : Type
*} [Preorder β] [Preorder γ] [h₁ : WellFoundedLT β] [h₂ : WellFoundedLT γ] (K : 
α) (f₁ : β -> α) (f…
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Submodule.ker_liftQ_eq_bot`：ker_liftQ_eq_bot (f : M ->ₛₗ[τ₁₂] M₂) (h) (h
' : ker f <= p) : ker (p.liftQ f h) = ⊥
· 使用定理 `LinearMap.surjective_rangeRestrict`：surjective_rangeRestrict : Surjectiv
e f.rangeRestrict
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_comap_eq`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} 
{M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
· 使用定理 `Submodule.range_liftQ`：range_liftQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ
₁₂] M₂) (h) : range (p.liftQ f h) = range f
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
· 使用定理 `LinearMap.ker_codRestrict`：ker_codRestrict (p : Submodule R₂ M₂) (f : M 
->ₛₗ[τ₁₂] M₂) (hf) : ker (codRestrict p f hf) = ker f
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
-/
theorem isArtinian_of_range_eq_ker [IsArtinian R M] [IsArtinian R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (h : LinearMap.range f = LinearMap.ker g) : IsArtinian R N :=
  wellFounded_lt_exact_sequence (LinearMap.range f)
    (Submodule.map ((LinearMap.ker f).liftQ f le_rfl))
    (Submodule.comap ((LinearMap.ker f).liftQ f le_rfl))
    (Submodule.comap g.rangeRestrict) (Submodule.map g.rangeRestrict)
    (Submodule.gciMapComap <| LinearMap.ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
    (Submodule.giMapComap g.surjective_rangeRestrict)
    (by simp [Submodule.map_comap_eq, inf_comm, Submodule.range_liftQ])
    (by simp [Submodule.comap_map_eq, h])
/-
**isArtinian_iff_submodule_quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isArtinian_iff_submodule_quotient (S : Submodule R P) : IsArtinian R P ↔ I
sArtinian R S ∧ IsArtinian R (P ⧸ S)
参数：S : Submodule R P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isArtinian_of_range_eq_ker`：isArtinian_of_range_eq_ker [IsArtinian R M] 
[IsArtinian R P] (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (h : LinearMap.range f = Line
arMap.ker g) : I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
-/
theorem isArtinian_iff_submodule_quotient (S : Submodule R P) :
    IsArtinian R P ↔ IsArtinian R S ∧ IsArtinian R (P ⧸ S) := by
  refine ⟨fun h ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ?_⟩
  apply isArtinian_of_range_eq_ker S.subtype S.mkQ
  rw [Submodule.ker_mkQ, Submodule.range_subtype]
/-
**isArtinian_prod** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isArtinian_prod [IsArtinian R M] [IsArtinian R P] : IsArtinian R (M × P)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isArtinian_of_range_eq_ker`：isArtinian_of_range_eq_ker [IsArtinian R M] 
[IsArtinian R P] (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (h : LinearMap.range f = Line
arMap.ker g) : I…
· 使用定理 `LinearMap.range_inl`：range_inl : range (inl R M M₂) = ker (snd R M M₂)
-/
instance isArtinian_prod [IsArtinian R M] [IsArtinian R P] : IsArtinian R (M × P) :=
  isArtinian_of_range_eq_ker (LinearMap.inl R M P) (LinearMap.snd R M P) (LinearMap.range_inl R M P)
/-
**isArtinian_sup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isArtinian_sup (M₁ M₂ : Submodule R P) [IsArtinian R M₁] [IsArtinian R M₂]
 : IsArtinian R ↥(M₁ ⊔ M₂)
参数：M₁ M₂ : Submodule R P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `LinearMap.range_coprod`：range_coprod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃
) : range (f.coprod g) = range f ⊔ range g
-/
instance isArtinian_sup (M₁ M₂ : Submodule R P) [IsArtinian R M₁] [IsArtinian R M₂] :
    IsArtinian R ↥(M₁ ⊔ M₂) := by
  have := isArtinian_range (M₁.subtype.coprod M₂.subtype)
  rwa [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype] at this

variable {ι : Type*} [Finite ι]
/-
**isArtinian_pi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isArtinian_pi : forall {M : ι -> Type*} [Π i, AddCommGroup (M i)] [Π i, Mo
dule R (M i)] [forall i, IsArtinian R (M i)], IsArtinian R (Π i, M i)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.induction_empty_option`：Finite.induction_empty_option {P : Type u
 -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β) (h_empty : P PEmpty) (h
_option : forall {α…
· 使用定理 `isArtinian_of_linearEquiv`：isArtinian_of_linearEquiv (f : M ≃ₗ[R] P) [Is
Artinian R M] : IsArtinian R P
· 使用定理 `Finite.to_wellFoundedLT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedLT α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
instance isArtinian_pi :
    ∀ {M : ι → Type*} [Π i, AddCommGroup (M i)]
      [Π i, Module R (M i)] [∀ i, IsArtinian R (M i)], IsArtinian R (Π i, M i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h ↦ isArtinian_of_linearEquiv (LinearEquiv.piCongrLeft R _ e)
  · infer_instance
  · exact fun ih ↦ isArtinian_of_linearEquiv (LinearEquiv.piOptionEquivProd R).symm

/-- A version of `isArtinian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
/-
**isArtinian_pi'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isArtinian_pi' [IsArtinian R M] : IsArtinian R (ι -> M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `isArtinian_pi` for non-dependent functions. We need this instance 
because
sometimes Lean fails to apply the dependent version in non-dependent settings (e
.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`).
-/
instance isArtinian_pi' [IsArtinian R M] : IsArtinian R (ι → M) :=
  isArtinian_pi
/-
**isArtinian_finsupp** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isArtinian_finsupp [IsArtinian R M] : IsArtinian R (ι ->₀ M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isArtinian_of_linearEquiv`：isArtinian_of_linearEquiv (f : M ≃ₗ[R] P) [Is
Artinian R M] : IsArtinian R P
-/
instance isArtinian_finsupp [IsArtinian R M] : IsArtinian R (ι →₀ M) :=
  isArtinian_of_linearEquiv (Finsupp.linearEquivFunOnFinite _ _ _).symm
/-
**isArtinian_iSup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isArtinian_iSup : forall {M : ι -> Submodule R P} [forall i, IsArtinian R 
(M i)], IsArtinian R ↥(⨆ i, M i)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.induction_empty_option`：Finite.induction_empty_option {P : Type u
 -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β) (h_empty : P PEmpty) (h
_option : forall {α…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.iSup_comp`：Equiv.iSup_comp {g : ι' -> α} (e : ι ≃ ι') : ⨆ x, g (e 
x) = ⨆ y, g y
· 使用定理 `iSup_of_empty`：iSup_of_empty [IsEmpty ι] (f : ι -> α) : iSup f = ⊥
· 使用定理 `Finite.to_wellFoundedLT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedLT α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `iSup_option`：iSup_option (f : Option β -> α) : ⨆ o, f o = f none ⊔ ⨆ b, 
f (Option.some b)
-/
instance isArtinian_iSup :
    ∀ {M : ι → Submodule R P} [∀ i, IsArtinian R (M i)], IsArtinian R ↥(⨆ i, M i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · intro _ _ e h _ _; rw [← e.iSup_comp]; apply h
  · intros; rw [iSup_of_empty]; infer_instance
  · intro _ _ ih _ _; rw [iSup_option]; infer_instance

variable (R M) in
/-
**IsArtinian.isSemisimpleModule_iff_jacobson** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsArtinian.isSemisimpleModule_iff_jacobson [IsArtinian R M] : IsSemisimple
Module R M ↔ Module.jacobson R M = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemisimpleModule.jacobson_eq_bot`：IsSemisimpleModule.jacobson_eq_bot [
IsSemisimpleModule R M] : Module.jacobson R M = ⊥
· 使用定理 `Finset.exists_inf_le`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilattic
eInf β] [inst_1 : OrderTop β] [WellFoundedLT β] (f : α → β),   ∃ t, ∀ (a : α), t
.inf f ≤ f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isSimpleModule_iff_isCoatom`：isSimpleModule_iff_isCoatom : IsSimpleModul
e R (M ⧸ m) ↔ IsCoatom m
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsSemisimpleModule.of_injective`：of_injective (f : N ->ₗ[R] M) (hf : Fun
ction.Injective f) : IsSemisimpleModule R N
· 使用定理 `instIsSemisimpleModuleForallOfFinite`：∀ {R : Type u_2} [inst : Ring R] {
ι : Type u_7} [Finite ι] (M : ι → Type u_6) [inst_2 : (i : ι) → AddCommGroup (M 
i)]   [inst_3 : (i : ι) → …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.jacobson.eq_1`：∀ (R : Type u_1) (M : Type u_3) [inst : Ring R] [i
nst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   Module.jacobson R M = sI
nf {m | Is…
· 使用定理 `Submodule.mem_sInf`：mem_sInf {S : Set (Submodule R M)} {x : M} : x in sI
nf S ↔ forall p in S, x in p
· 使用定理 `Submodule.mem_finsetInf`：mem_finsetInf {ι} {s : Finset ι} {p : ι -> Subm
odule R M} {x : M} : x in s.inf p ↔ forall i in s, x in p i
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem IsArtinian.isSemisimpleModule_iff_jacobson [IsArtinian R M] :
    IsSemisimpleModule R M ↔ Module.jacobson R M = ⊥ :=
  ⟨fun _ ↦ IsSemisimpleModule.jacobson_eq_bot R M, fun h ↦
    have ⟨s, hs⟩ := Finset.exists_inf_le (Subtype.val (p := fun m : Submodule R M ↦ IsCoatom m))
    have _ (m : s) : IsSimpleModule R (M ⧸ m.1.1) := isSimpleModule_iff_isCoatom.mpr m.1.2
    let f : M →ₗ[R] ∀ m : s, M ⧸ m.1.1 := LinearMap.pi fun m ↦ m.1.1.mkQ
    .of_injective f <| LinearMap.ker_eq_bot.mp <| le_bot_iff.mp fun x hx ↦ by
      rw [← h, Module.jacobson, Submodule.mem_sInf]
      exact fun m hm ↦ hs ⟨m, hm⟩ <| Submodule.mem_finsetInf.mpr fun i hi ↦
        (Submodule.Quotient.mk_eq_zero i.1).mp <| congr_fun hx ⟨i, hi⟩⟩

open Submodule Function

namespace LinearMap

variable [IsArtinian R M]

/-- For any endomorphism of an Artinian module, any sufficiently high iterate has codisjoint kernel
and range. -/
/-
**LinearMap.eventually_codisjoint_ker_pow_range_pow** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap`。
形式化陈述：eventually_codisjoint_ker_pow_range_pow (f : Module.End R M) : forallᶠ n i
n atTop, Codisjoint (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n))
参数：f : Module.End R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinian.monotone_stabilizes`：monotone_stabilizes (f : Nat ->o (Submod
ule R M)ᵒᵈ) : exists n, forall m, n <= m -> f n = f m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.End.pow_apply`：pow_apply (f : End R M) (n : Nat) (m : M) : (f ^ n
) m = f^[n] m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.mem_range`：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] 
M₂} {x} : x in range f ↔ exists y, f y = x
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
For any endomorphism of an Artinian module, any sufficiently high iterate has co
disjoint kernel
and range.
-/
theorem eventually_codisjoint_ker_pow_range_pow (f : Module.End R M) :
    ∀ᶠ n in atTop, Codisjoint (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  obtain ⟨n, hn : ∀ m, n ≤ m → LinearMap.range (f ^ n) = LinearMap.range (f ^ m)⟩ :=
    IsArtinian.monotone_stabilizes f.iterateRange
  refine eventually_atTop.mpr ⟨n, fun m hm ↦ codisjoint_iff.mpr ?_⟩
  simp_rw [← hn _ hm, Submodule.eq_top_iff', Submodule.mem_sup]
  intro x
  rsuffices ⟨y, hy⟩ : ∃ y, (f ^ m) ((f ^ n) y) = (f ^ m) x
  · exact ⟨x - (f ^ n) y, by simp [hy], (f ^ n) y, by simp⟩
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `mem_range` into `mem_range (f := _)`
  simp_rw [f.pow_apply n, f.pow_apply m, ← iterate_add_apply, ← f.pow_apply (m + n),
    ← f.pow_apply m, ← mem_range (f := _), ← hn _ (n.le_add_left m), hn _ hm]
  exact LinearMap.mem_range_self (f ^ m) x

/-- This is the Fitting decomposition of the module `M` with respect to the endomorphism `f`.

See also `LinearMap.isCompl_iSup_ker_pow_iInf_range_pow` for an alternative spelling. -/
/-
**LinearMap.eventually_isCompl_ker_pow_range_pow** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
形式化陈述：eventually_isCompl_ker_pow_range_pow [IsNoetherian R M] (f : Module.End R 
M) : forallᶠ n in atTop, IsCompl (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n
))
参数：f : Module.End R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Module.End.eventually_disjoint_ker_pow_range_pow`：Module.End.eventually_
disjoint_ker_pow_range_pow (f : End R M) : forallᶠ n in atTop, Disjoint (LinearM
ap.ker (f ^ n)) (LinearMap.range (f ^ …
· 使用定理 `LinearMap.eventually_codisjoint_ker_pow_range_pow`：eventually_codisjoint
_ker_pow_range_pow (f : Module.End R M) : forallᶠ n in atTop, Codisjoint (Linear
Map.ker (f ^ n)) (LinearMap.range (f ^ …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
This is the Fitting decomposition of the module `M` with respect to the endomorp
hism `f`.

See also `LinearMap.isCompl_iSup_ker_pow_iInf_range_pow` for an alternative spel
ling.
-/
theorem eventually_isCompl_ker_pow_range_pow [IsNoetherian R M] (f : Module.End R M) :
    ∀ᶠ n in atTop, IsCompl (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  filter_upwards [f.eventually_disjoint_ker_pow_range_pow.and
    f.eventually_codisjoint_ker_pow_range_pow] with n hn
  simpa only [isCompl_iff]

/-- This is the Fitting decomposition of the module `M` with respect to the endomorphism `f`.

See also `LinearMap.eventually_isCompl_ker_pow_range_pow` for an alternative spelling. -/
/-
**LinearMap.isCompl_iSup_ker_pow_iInf_range_pow** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap`。
形式化陈述：isCompl_iSup_ker_pow_iInf_range_pow [IsNoetherian R M] (f : M ->ₗ[R] M) : 
IsCompl (⨆ n, LinearMap.ker (f ^ n)) (⨅ n, LinearMap.range (f ^ n))
参数：f : M ->ₗ[R] M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `LinearMap.eventually_isCompl_ker_pow_range_pow`：eventually_isCompl_ker_p
ow_range_pow [IsNoetherian R M] (f : Module.End R M) : forallᶠ n in atTop, IsCom
pl (LinearMap.ker (f ^ n)) (LinearMa…
· 使用引理 `LinearMap.eventually_iInf_range_pow_eq`：eventually_iInf_range_pow_eq (f 
: Module.End R M) : forallᶠ n in atTop, ⨅ m, LinearMap.range (f ^ m) = LinearMap
.range (f ^ n)
· 使用引理 `LinearMap.eventually_iSup_ker_pow_eq`：LinearMap.eventually_iSup_ker_pow_
eq (f : M ->ₗ[R] M) : forallᶠ n in atTop, ⨆ m, LinearMap.ker (f ^ m) = LinearMap
.ker (f ^ n)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
This is the Fitting decomposition of the module `M` with respect to the endomorp
hism `f`.

See also `LinearMap.eventually_isCompl_ker_pow_range_pow` for an alternative spe
lling.
-/
theorem isCompl_iSup_ker_pow_iInf_range_pow [IsNoetherian R M] (f : M →ₗ[R] M) :
    IsCompl (⨆ n, LinearMap.ker (f ^ n)) (⨅ n, LinearMap.range (f ^ n)) := by
  obtain ⟨k, hk⟩ := eventually_atTop.mp <| f.eventually_isCompl_ker_pow_range_pow.and <|
    f.eventually_iInf_range_pow_eq.and f.eventually_iSup_ker_pow_eq
  obtain ⟨h₁, h₂, h₃⟩ := hk k (le_refl k)
  rwa [h₂, h₃]

end LinearMap

end Ring

section CommSemiring

variable {R : Type*} (M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] [IsArtinian R M]

namespace IsArtinian

/-
**IsArtinian.range_smul_pow_stabilizes** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinian`。
形式化陈述：range_smul_pow_stabilizes (r : R) : exists n : Nat, forall m, n <= m -> Li
nearMap.range (r ^ n • LinearMap.id : M ->ₗ[R] M) = LinearMap.range (r ^ m • Lin
earMap.id : M ->ₗ[R] M)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinian.monotone_stabilizes`：monotone_stabilizes (f : Nat ->o (Submod
ule R M)ᵒᵈ) : exists n, forall m, n <= m -> f n = f m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem range_smul_pow_stabilizes (r : R) :
    ∃ n : ℕ, ∀ m, n ≤ m →
      LinearMap.range (r ^ n • LinearMap.id : M →ₗ[R] M) =
      LinearMap.range (r ^ m • LinearMap.id : M →ₗ[R] M) :=
  monotone_stabilizes
    ⟨fun n => LinearMap.range (r ^ n • LinearMap.id : M →ₗ[R] M), fun n m h x ⟨y, hy⟩ =>
      ⟨r ^ (m - n) • y, by
        dsimp at hy ⊢
        rw [← smul_assoc, smul_eq_mul, ← pow_add, ← hy, add_tsub_cancel_of_le h]⟩⟩

variable {M}
/-
**IsArtinian.exists_pow_succ_smul_dvd** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinian`。
形式化陈述：exists_pow_succ_smul_dvd (r : R) (x : M) : exists (n : Nat) (y : M), r ^ n
.succ • y = r ^ n • x
参数：r : R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinian.range_smul_pow_stabilizes`：range_smul_pow_stabilizes (r : R) 
: exists n : Nat, forall m, n <= m -> LinearMap.range (r ^ n • LinearMap.id : M 
->ₗ[R] M) = LinearMap.rang…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem exists_pow_succ_smul_dvd (r : R) (x : M) :
    ∃ (n : ℕ) (y : M), r ^ n.succ • y = r ^ n • x := by
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes M r
  simp_rw [SetLike.ext_iff] at hn
  exact ⟨n, by simpa using hn n.succ n.le_succ (r ^ n • x)⟩

end IsArtinian

end CommSemiring

/-
**isArtinian_of_submodule_of_artinian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isArtinian_of_submodule_of_artinian (R M) [Semiring R] [AddCommMonoid M] [
Module R M] (N : Submodule R M) (_ : IsArtinian R M) : IsArtinian R N
参数：R M；N : Submodule R M；_ : IsArtinian R M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isArtinian_of_submodule_of_artinian (R M) [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (_ : IsArtinian R M) : IsArtinian R N := inferInstance

/-- If `M / S / R` is a scalar tower, and `M / R` is Artinian, then `M / S` is also Artinian. -/
/-
**isArtinian_of_tower** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isArtinian_of_tower (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] 
[SMul R S] [Module S M] [Module R M] [IsScalarTower R S M] (h : IsArtinian R M) 
: IsArtinian S M
参数：R；h : IsArtinian R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.wellFounded`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β] (f : α ↪o β),   (WellFounded fun x1 x2 => x1 < x2)
 → WellFounded f…
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r

--- 原说明 ---
If `M / S / R` is a scalar tower, and `M / R` is Artinian, then `M / S` is also 
Artinian.
-/
theorem isArtinian_of_tower (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] [SMul R S]
    [Module S M] [Module R M] [IsScalarTower R S M] (h : IsArtinian R M) : IsArtinian S M :=
  ⟨(Submodule.restrictScalarsEmbedding R S M).wellFounded h.wf⟩
/-
**DivisionSemiring.instIsArtinianRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：DivisionSemiring.instIsArtinianRing {K : Type*} [DivisionSemiring K] : IsA
rtinianRing K
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.wellFounded_of_trans_of_irrefl`：wellFounded_of_trans_of_irrefl (r
 : α -> α -> Prop) [IsTrans α r] [Std.Irrefl r] : WellFounded r
· 使用定理 `Ideal.instFinite`：∀ {K : Type u_5} [inst : DivisionSemiring K], Finite (
Ideal K)
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
instance DivisionSemiring.instIsArtinianRing {K : Type*} [DivisionSemiring K] : IsArtinianRing K :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩
/-
**DivisionRing.instIsArtinianRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：DivisionRing.instIsArtinianRing {K : Type*} [DivisionRing K] : IsArtinianR
ing K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance DivisionRing.instIsArtinianRing {K : Type*} [DivisionRing K] : IsArtinianRing K :=
  inferInstance
/-
**Ring.isArtinian_of_zero_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.isArtinian_of_zero_eq_one {R} [Semiring R] (h01 : (0 : R) = 1) : IsAr
tinianRing R
参数：h01 : (0 : R) = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_zero_eq_one`：∀ {M₀ : Type u_1} [inst : MulZeroOneClass M
₀], 0 = 1 → Subsingleton M₀
· 使用定理 `Finite.to_wellFoundedLT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedLT α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem Ring.isArtinian_of_zero_eq_one {R} [Semiring R] (h01 : (0 : R) = 1) : IsArtinianRing R :=
  have := subsingleton_of_zero_eq_one h01
  inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R) [Ring R] [IsArtinianRing R] (I : Ideal R) [I.IsTwoSided] : IsArtinianRing (R ⧸ I) :=
  isArtinian_of_tower R inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) (R) [Semiring R] [IsArtinianRing R] : IsDedekindFiniteMonoid R where
  mul_eq_one_symm {a b} hab := by
    have ⟨c, hca⟩ := IsArtinian.surjective_of_injective_endomorphism
      (.toSpanSingleton R R a) (isRightRegular_of_mul_eq_one hab) 1
    rwa [← left_inv_eq_right_inv hca hab]

open Submodule Function
/-
**isArtinian_of_fg_of_artinian'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isArtinian_of_fg_of_artinian' {R M} [Ring R] [AddCommGroup M] [Module R M]
 [IsArtinianRing R] [Module.Finite R M] : IsArtinian R M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
· 使用定理 `isArtinian_of_surjective`：isArtinian_of_surjective (f : M ->ₗ[R] P) (hf 
: Function.Surjective f) [IsArtinian R M] : IsArtinian R P
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance isArtinian_of_fg_of_artinian' {R M} [Ring R] [AddCommGroup M] [Module R M]
    [IsArtinianRing R] [Module.Finite R M] : IsArtinian R M :=
  have ⟨_, _, h⟩ := Module.Finite.exists_fin' R M
  isArtinian_of_surjective _ _ h
/-
**isArtinian_of_fg_of_artinian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isArtinian_of_fg_of_artinian {R M} [Ring R] [AddCommGroup M] [Module R M] 
(N : Submodule R M) [IsArtinianRing R] (hN : N.FG) : IsArtinian R N
参数：N : Submodule R M；hN : N.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
-/
theorem isArtinian_of_fg_of_artinian {R M} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [IsArtinianRing R] (hN : N.FG) : IsArtinian R N := by
  rw [← Module.Finite.iff_fg] at hN; infer_instance
/-
**IsArtinianRing.of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsArtinianRing.of_finite (R S) [Ring R] [Ring S] [Module R S] [IsScalarTow
er R S S] [IsArtinianRing R] [Module.Finite R S] : IsArtinianRing S
参数：R S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isArtinian_of_tower`：isArtinian_of_tower (R) {S M} [Semiring R] [Semirin
g S] [AddCommMonoid M] [SMul R S] [Module S M] [Module R M] [IsScalarTower R S M
] (h : Is…
-/
theorem IsArtinianRing.of_finite (R S) [Ring R] [Ring S] [Module R S] [IsScalarTower R S S]
    [IsArtinianRing R] [Module.Finite R S] : IsArtinianRing S :=
  isArtinian_of_tower R isArtinian_of_fg_of_artinian'
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n R) [Fintype n] [DecidableEq n] [Ring R] [IsNoetherianRing R] :
    IsNoetherianRing (Matrix n n R) := .of_finite R _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n R) [Fintype n] [DecidableEq n] [Ring R] [IsArtinianRing R] :
    IsArtinianRing (Matrix n n R) := .of_finite R _

/-- In a module over an Artinian ring, the submodule generated by finitely many vectors is
Artinian. -/
/-
**isArtinian_span_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isArtinian_span_of_finite (R) {M} [Ring R] [AddCommGroup M] [Module R M] [
IsArtinianRing R] {A : Set M} (hA : A.Finite) : IsArtinian R (Submodule.span R A
)
参数：R；hA : A.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isArtinian_of_fg_of_artinian`：isArtinian_of_fg_of_artinian {R M} [Ring R
] [AddCommGroup M] [Module R M] (N : Submodule R M) [IsArtinianRing R] (hN : N.F
G) : IsArtinian R …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N

--- 原说明 ---
In a module over an Artinian ring, the submodule generated by finitely many vect
ors is
Artinian.
-/
theorem isArtinian_span_of_finite (R) {M} [Ring R] [AddCommGroup M] [Module R M] [IsArtinianRing R]
    {A : Set M} (hA : A.Finite) : IsArtinian R (Submodule.span R A) :=
  isArtinian_of_fg_of_artinian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)
/-
**Function.Surjective.isArtinianRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.isArtinianRing {R} [Semiring R] {S} [Semiring S] {F} [
FunLike F R S] [RingHomClass F R S] {f : F} (hf : Function.Surjective f) [H : Is
ArtinianRing R] : IsArtinianRing S
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isArtinianRing_iff`：isArtinianRing_iff {R} [Semiring R] : IsArtinianRing
 R ↔ IsArtinian R R
· 使用定理 `OrderEmbedding.wellFounded`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β] (f : α ↪o β),   (WellFounded fun x1 x2 => x1 < x2)
 → WellFounded f…
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
theorem Function.Surjective.isArtinianRing {R} [Semiring R] {S} [Semiring S] {F}
    [FunLike F R S] [RingHomClass F R S]
    {f : F} (hf : Function.Surjective f) [H : IsArtinianRing R] : IsArtinianRing S := by
  rw [isArtinianRing_iff] at H ⊢
  exact ⟨(Ideal.orderEmbeddingOfSurjective f hf).wellFounded H.wf⟩
/-
**isArtinianRing_rangeS** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isArtinianRing_rangeS {R} [Semiring R] {S} [Semiring S] (f : R ->+* S) [Is
ArtinianRing R] : IsArtinianRing f.rangeS
参数：f : R ->+* S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.isArtinianRing`：Function.Surjective.isArtinianRing {
R} [Semiring R] {S} [Semiring S] {F} [FunLike F R S] [RingHomClass F R S] {f : F
} (hf : Function.Surject…
· 使用定理 `RingHom.rangeSRestrict_surjective`：rangeSRestrict_surjective (f : R ->+*
 S) : Function.Surjective f.rangeSRestrict
-/
instance isArtinianRing_rangeS {R} [Semiring R] {S} [Semiring S] (f : R →+* S) [IsArtinianRing R] :
    IsArtinianRing f.rangeS :=
  f.rangeSRestrict_surjective.isArtinianRing
/-
**isArtinianRing_range** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isArtinianRing_range {R} [Ring R] {S} [Ring S] (f : R ->+* S) [IsArtinianR
ing R] : IsArtinianRing f.range
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isArtinianRing_range {R} [Ring R] {S} [Ring S] (f : R →+* S) [IsArtinianRing R] :
    IsArtinianRing f.range :=
  isArtinianRing_rangeS f
/-
**RingEquiv.isArtinianRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingEquiv.isArtinianRing {R S} [Semiring R] [Semiring S] (f : R ≃+* S) [Is
ArtinianRing R] : IsArtinianRing S
参数：f : R ≃+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.isArtinianRing`：Function.Surjective.isArtinianRing {
R} [Semiring R] {S} [Semiring S] {F} [FunLike F R S] [RingHomClass F R S] {f : F
} (hf : Function.Surject…
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
theorem RingEquiv.isArtinianRing {R S} [Semiring R] [Semiring S] (f : R ≃+* S)
    [IsArtinianRing R] : IsArtinianRing S :=
  f.surjective.isArtinianRing
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S} [Semiring R] [Semiring S] [IsArtinianRing R] [IsArtinianRing S] :
    IsArtinianRing (R × S) :=
  Ideal.idealProdEquiv.toOrderEmbedding.wellFoundedLT
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι} [Finite ι] : ∀ {R : ι → Type*} [Π i, Semiring (R i)] [∀ i, IsArtinianRing (R i)],
    IsArtinianRing (Π i, R i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h ↦ RingEquiv.isArtinianRing (.piCongrLeft _ e)
  · infer_instance
  · exact fun ih ↦ RingEquiv.isArtinianRing (.symm .piOptionEquivProd)

namespace IsArtinianRing

section Semiring

variable {R : Type*} [Semiring R]

/-
**IsArtinianRing.isUnit_iff_isRightRegular** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinian
Ring`。
形式化陈述：isUnit_iff_isRightRegular [IsArtinianRing R] {x : R} : IsUnit x ↔ IsRightR
egular x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsRightRegular.eq_1`：∀ {R : Type u_1} [inst : Mul R] (c : R), IsRightReg
ular c = Function.Injective fun x => x * c
· 使用定理 `IsUnit.isUnit_iff_mulRight_bijective`：isUnit_iff_mulRight_bijective {a :
 M} : IsUnit a ↔ Function.Bijective (· * a)
· 使用定理 `Function.Bijective.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} (f : α → β), Func
tion.Bijective f = (Function.Injective f ∧ Function.Surjective f)
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `IsArtinian.surjective_of_injective_endomorphism`：surjective_of_injective
_endomorphism (f : M ->ₗ[R] M) (s : Injective f) : Surjective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUnit_iff_isRightRegular [IsArtinianRing R] {x : R} : IsUnit x ↔ IsRightRegular x := by
  rw [IsRightRegular, IsUnit.isUnit_iff_mulRight_bijective, Bijective, and_iff_left_of_imp]
  exact IsArtinian.surjective_of_injective_endomorphism (.toSpanSingleton R R x)
/-
**IsArtinianRing.isUnit_iff_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinianRing`
。
形式化陈述：isUnit_iff_isRegular [IsArtinianRing R] {x : R} : IsUnit x ↔ IsRegular x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isRegular_iff`：isRegular_iff {c : R} : IsRegular c ↔ IsLeftRegular c ∧ I
sRightRegular c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsArtinianRing.isUnit_iff_isRightRegular`：isUnit_iff_isRightRegular [IsA
rtinianRing R] {x : R} : IsUnit x ↔ IsRightRegular x
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `IsUnit.isRegular`：IsUnit.isRegular (ua : IsUnit a) : IsRegular a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUnit_iff_isRegular [IsArtinianRing R] {x : R} : IsUnit x ↔ IsRegular x := by
  rw [isRegular_iff, ← isUnit_iff_isRightRegular, and_iff_right_of_imp (·.isRegular.1)]
/-
**IsArtinianRing.isUnit_iff_isLeftRegular** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinianR
ing`。
形式化陈述：isUnit_iff_isLeftRegular [IsArtinianRing Rᵐᵒᵖ] {x : R} : IsUnit x ↔ IsLeft
Regular x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isRightRegular_op`：isRightRegular_op {a : R} : IsRightRegular (op a) ↔ I
sLeftRegular a
· 使用定理 `isUnit_op`：isUnit_op {M} [Monoid M] {m : M} : IsUnit (op m) ↔ IsUnit m
· 使用定理 `IsArtinianRing.isUnit_iff_isRightRegular`：isUnit_iff_isRightRegular [IsA
rtinianRing R] {x : R} : IsUnit x ↔ IsRightRegular x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUnit_iff_isLeftRegular [IsArtinianRing Rᵐᵒᵖ] {x : R} : IsUnit x ↔ IsLeftRegular x := by
  rw [← isRightRegular_op, ← isUnit_op, isUnit_iff_isRightRegular]
/-
**IsArtinianRing.isUnit_iff_isRegular_of_mulOpposite** 是 Mathlib 中的一个定理，位于命名空间 `
IsArtinianRing`。
形式化陈述：isUnit_iff_isRegular_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] {x : R} : IsUnit
 x ↔ IsRegular x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isRegular_iff`：isRegular_iff {c : R} : IsRegular c ↔ IsLeftRegular c ∧ I
sRightRegular c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsArtinianRing.isUnit_iff_isLeftRegular`：isUnit_iff_isLeftRegular [IsArt
inianRing Rᵐᵒᵖ] {x : R} : IsUnit x ↔ IsLeftRegular x
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
· 使用定理 `IsUnit.isRegular`：IsUnit.isRegular (ua : IsUnit a) : IsRegular a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUnit_iff_isRegular_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] {x : R} :
    IsUnit x ↔ IsRegular x := by
  rw [isRegular_iff, ← isUnit_iff_isLeftRegular, and_iff_left_of_imp (·.isRegular.2)]

end Semiring

section Ring

variable {R : Type*} [Ring R]

open nonZeroDivisors

/-- If an element of an Artinian ring is not a zero divisor then it is a unit. -/
/-
**IsArtinianRing.isUnit_of_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `IsArti
nianRing`。
形式化陈述：isUnit_of_mem_nonZeroDivisors [IsArtinianRing R] {a : R} (ha : a in R⁰) : 
IsUnit a
参数：ha : a in R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsArtinianRing.isUnit_iff_isRegular`：isUnit_iff_isRegular [IsArtinianRin
g R] {x : R} : IsUnit x ↔ IsRegular x
· 使用引理 `isRegular_iff_mem_nonZeroDivisors`：isRegular_iff_mem_nonZeroDivisors : I
sRegular r ↔ r in R⁰

--- 原说明 ---
If an element of an Artinian ring is not a zero divisor then it is a unit.
-/
theorem isUnit_of_mem_nonZeroDivisors [IsArtinianRing R] {a : R} (ha : a ∈ R⁰) : IsUnit a := by
  rwa [isUnit_iff_isRegular, isRegular_iff_mem_nonZeroDivisors]
/-
**IsArtinianRing.isUnit_of_mem_nonZeroDivisors_of_mulOpposite** 是 Mathlib 中的一个定理
，位于命名空间 `IsArtinianRing`。
形式化陈述：isUnit_of_mem_nonZeroDivisors_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] {a : R}
 (ha : a in R⁰) : IsUnit a
参数：ha : a in R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsArtinianRing.isUnit_iff_isRegular_of_mulOpposite`：isUnit_iff_isRegular
_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] {x : R} : IsUnit x ↔ IsRegular x
· 使用引理 `isRegular_iff_mem_nonZeroDivisors`：isRegular_iff_mem_nonZeroDivisors : I
sRegular r ↔ r in R⁰
-/
theorem isUnit_of_mem_nonZeroDivisors_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] {a : R}
    (ha : a ∈ R⁰) : IsUnit a := by
  rwa [isUnit_iff_isRegular_of_mulOpposite, isRegular_iff_mem_nonZeroDivisors]

/-- In an Artinian ring, an element is a unit iff it is a non-zero-divisor.
See also `isUnit_iff_mem_nonZeroDivisors_of_finite`. -/
/-
**IsArtinianRing.isUnit_iff_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `IsArt
inianRing`。
形式化陈述：isUnit_iff_mem_nonZeroDivisors [IsArtinianRing R] {a : R} : IsUnit a ↔ a i
n R⁰
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsArtinianRing.isUnit_iff_isRegular`：isUnit_iff_isRegular [IsArtinianRin
g R] {x : R} : IsUnit x ↔ IsRegular x
· 使用引理 `isRegular_iff_mem_nonZeroDivisors`：isRegular_iff_mem_nonZeroDivisors : I
sRegular r ↔ r in R⁰
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
In an Artinian ring, an element is a unit iff it is a non-zero-divisor.
See also `isUnit_iff_mem_nonZeroDivisors_of_finite`.
-/
theorem isUnit_iff_mem_nonZeroDivisors [IsArtinianRing R] {a : R} : IsUnit a ↔ a ∈ R⁰ := by
  rw [isUnit_iff_isRegular, isRegular_iff_mem_nonZeroDivisors]
/-
**IsArtinianRing.isUnit_iff_mem_nonZeroDivisors_of_mulOpposite** 是 Mathlib 中的一个定
理，位于命名空间 `IsArtinianRing`。
形式化陈述：isUnit_iff_mem_nonZeroDivisors_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] {a : R
} : IsUnit a ↔ a in R⁰
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsArtinianRing.isUnit_iff_isRegular_of_mulOpposite`：isUnit_iff_isRegular
_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] {x : R} : IsUnit x ↔ IsRegular x
· 使用引理 `isRegular_iff_mem_nonZeroDivisors`：isRegular_iff_mem_nonZeroDivisors : I
sRegular r ↔ r in R⁰
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUnit_iff_mem_nonZeroDivisors_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] {a : R} :
    IsUnit a ↔ a ∈ R⁰ := by
  rw [isUnit_iff_isRegular_of_mulOpposite, isRegular_iff_mem_nonZeroDivisors]

variable (R)
/-
**IsArtinianRing.isUnitSubmonoid_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinianRing`。
形式化陈述：isUnitSubmonoid_eq [IsArtinianRing R] : IsUnit.submonoid R = R⁰
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUnitSubmonoid_eq [IsArtinianRing R] : IsUnit.submonoid R = R⁰ := by
  ext; simp [IsUnit.mem_submonoid_iff, isUnit_iff_mem_nonZeroDivisors]
/-
**IsArtinianRing.isUnitSubmonoid_eq_of_mulOpposite** 是 Mathlib 中的一个定理，位于命名空间 `Is
ArtinianRing`。
形式化陈述：isUnitSubmonoid_eq_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] : IsUnit.submonoid
 R = R⁰
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUnitSubmonoid_eq_of_mulOpposite [IsArtinianRing Rᵐᵒᵖ] :
    IsUnit.submonoid R = R⁰ := by
  ext; simp [IsUnit.mem_submonoid_iff, isUnit_iff_mem_nonZeroDivisors_of_mulOpposite]
/-
**IsArtinianRing.isUnitSubmonoid_eq_nonZeroDivisorsRight** 是 Mathlib 中的一个定理，位于命名
空间 `IsArtinianRing`。
形式化陈述：isUnitSubmonoid_eq_nonZeroDivisorsRight [IsArtinianRing R] : IsUnit.submon
oid R = nonZeroDivisorsRight R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isRightRegular_iff_mem_nonZeroDivisorsRight`：isRightRegular_iff_mem_nonZ
eroDivisorsRight : IsRightRegular r ↔ r in nonZeroDivisorsRight R
· 使用定理 `IsArtinianRing.isUnit_iff_isRightRegular`：isUnit_iff_isRightRegular [IsA
rtinianRing R] {x : R} : IsUnit x ↔ IsRightRegular x
-/
theorem isUnitSubmonoid_eq_nonZeroDivisorsRight [IsArtinianRing R] :
    IsUnit.submonoid R = nonZeroDivisorsRight R := by
  ext; rw [← isRightRegular_iff_mem_nonZeroDivisorsRight]; exact isUnit_iff_isRightRegular
/-
**IsArtinianRing.nonZeroDivisorsLeft_eq_isUnitSubmonoid** 是 Mathlib 中的一个定理，位于命名空
间 `IsArtinianRing`。
形式化陈述：nonZeroDivisorsLeft_eq_isUnitSubmonoid [IsArtinianRing Rᵐᵒᵖ] : IsUnit.subm
onoid R = nonZeroDivisorsLeft R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isLeftRegular_iff_mem_nonZeroDivisorsLeft`：isLeftRegular_iff_mem_nonZero
DivisorsLeft : IsLeftRegular r ↔ r in nonZeroDivisorsLeft R
· 使用定理 `IsArtinianRing.isUnit_iff_isLeftRegular`：isUnit_iff_isLeftRegular [IsArt
inianRing Rᵐᵒᵖ] {x : R} : IsUnit x ↔ IsLeftRegular x
-/
theorem nonZeroDivisorsLeft_eq_isUnitSubmonoid [IsArtinianRing Rᵐᵒᵖ] :
    IsUnit.submonoid R = nonZeroDivisorsLeft R := by
  ext; rw [← isLeftRegular_iff_mem_nonZeroDivisorsLeft]; exact isUnit_iff_isLeftRegular

end Ring

section CommSemiring

variable (R : Type*) [CommSemiring R] [IsArtinianRing R]

@[stacks 00J7]
/-
**IsArtinianRing.setOfPred_isMaximal_finite** 是 Mathlib 中的一个引理，位于命名空间 `IsArtinia
nRing`。
形式化陈述：setOfPred_isMaximal_finite : {I : Ideal R | I.IsMaximal}.Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_inf_le`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilattic
eInf β] [inst_1 : OrderTop β] [WellFoundedLT β] (f : α → β),   ∃ t, ∀ (a : α), t
.inf f ≤ f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.finite_def`：finite_def {s : Set α} : s.Finite ↔ Nonempty (Fintype s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.IsPrime.inf_le'`：∀ {R : Type u} {ι : Type u_1} [inst : CommSemirin
g R] {s : Finset ι} {f : ι → Ideal R} {P : Ideal R},   P.IsPrime → (s.inf f ≤ P 
↔ ∃ i ∈ s, …
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
-/
lemma setOfPred_isMaximal_finite : {I : Ideal R | I.IsMaximal}.Finite := by
  have ⟨s, H⟩ := Finset.exists_inf_le (Subtype.val (p := fun I : Ideal R ↦ I.IsMaximal))
  refine Set.finite_def.2 ⟨s, fun p ↦ ?_⟩
  have ⟨q, hq1, hq2⟩ := p.2.isPrime.inf_le'.mp (H p)
  rwa [← Subtype.ext <| q.2.eq_of_le p.2.ne_top hq2]

@[deprecated (since := "2026-07-09")] alias setOf_isMaximal_finite := setOfPred_isMaximal_finite
/-
**IsArtinianRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsArtinianRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Finite (MaximalSpectrum R) :=
  haveI : Finite {I : Ideal R // I.IsMaximal} := (setOfPred_isMaximal_finite R).to_subtype
  .of_equiv _ (MaximalSpectrum.equivSubtype _).symm

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [IsArtinianRing R]

variable (R) in
/-
**IsArtinianRing.isField_of_isDomain** 是 Mathlib 中的一个引理，位于命名空间 `IsArtinianRing`。
形式化陈述：isField_of_isDomain [IsDomain R] : IsField R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nontrivial.exists_pair_ne`：∀ {α : Type u_3} [self : Nontrivial α], ∃ x y
, x ≠ y
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsArtinian.exists_pow_succ_smul_dvd`：exists_pow_succ_smul_dvd (r : R) (x
 : M) : exists (n : Nat) (y : M), r ^ n.succ • y = r ^ n • x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
-/
lemma isField_of_isDomain [IsDomain R] : IsField R := by
  refine ⟨Nontrivial.exists_pair_ne, mul_comm, fun {x} hx ↦ ?_⟩
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : R)
  replace hy : x ^ n * (x * y - 1) = 0 := by
    rw [mul_sub, sub_eq_zero]
    convert! hy using 1
    simp [Nat.succ_eq_add_one, pow_add, mul_assoc]
  rw [mul_eq_zero, sub_eq_zero] at hy
  exact ⟨_, hy.resolve_left <| pow_ne_zero _ hx⟩

/- Does not hold in a commutative semiring:
consider {0, 0.5, 1} with ⊔ as + and ⊓ as *, then both {0} and {0, 0.5} are prime ideals. -/
-- Note: type class synthesis should try to synthesize `p.IsPrime` before `IsArtinianRing R`,
-- hence the argument order.
/-
**IsArtinianRing.isMaximal_of_isPrime** 是 Mathlib 中的一个实例，位于命名空间 `IsArtinianRing`
。
形式化陈述：isMaximal_of_isPrime {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] [I
sArtinianRing R] : p.IsMaximal
参数：p : Ideal R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.maximal_of_isField`：maximal_of_isField {R} [CommRing R] (
I : Ideal R) (hqf : IsField (R ⧸ I)) : I.IsMaximal
· 使用引理 `IsArtinianRing.isField_of_isDomain`：isField_of_isDomain [IsDomain R] : I
sField R
· 使用定理 `instIsArtinianRingQuotientIdeal`：∀ (R : Type u_1) [inst : Ring R] [IsArt
inianRing R] (I : Ideal R) [inst_2 : I.IsTwoSided], IsArtinianRing (R ⧸ I)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
instance isMaximal_of_isPrime {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    [IsArtinianRing R] : p.IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ (isField_of_isDomain _)
/-
**IsArtinianRing.isPrime_iff_isMaximal** 是 Mathlib 中的一个引理，位于命名空间 `IsArtinianRing
`。
形式化陈述：isPrime_iff_isMaximal (p : Ideal R) : p.IsPrime ↔ p.IsMaximal
参数：p : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
-/
lemma isPrime_iff_isMaximal (p : Ideal R) : p.IsPrime ↔ p.IsMaximal :=
  ⟨fun _ ↦ isMaximal_of_isPrime p, fun h ↦ h.isPrime⟩
/-
**IsArtinianRing.mem_minimalPrimes** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinianRing`。
形式化陈述：mem_minimalPrimes {I p : Ideal R} [hp : p.IsPrime] (hIp : I <= p) : p in I
.minimalPrimes
参数：hIp : I <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
-/
theorem mem_minimalPrimes {I p : Ideal R} [hp : p.IsPrime] (hIp : I ≤ p) : p ∈ I.minimalPrimes :=
  ⟨⟨hp, hIp⟩, fun q ⟨_, _⟩ hqp ↦ ((isMaximal_of_isPrime q).eq_of_le hp.ne_top hqp).ge⟩

/-- The prime spectrum is in bijection with the maximal spectrum. -/
@[simps]
/-
**IsArtinianRing.primeSpectrumEquivMaximalSpectrum** 是 Mathlib 中的一个定义，位于命名空间 `Is
ArtinianRing`。
形式化陈述：primeSpectrumEquivMaximalSpectrum : PrimeSpectrum R ≃ MaximalSpectrum R wh
ere .mp I.isPrime⟩ toFun I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prime spectrum is in bijection with the maximal spectrum.
-/
def primeSpectrumEquivMaximalSpectrum : PrimeSpectrum R ≃ MaximalSpectrum R where
  toFun I := ⟨I.asIdeal, isPrime_iff_isMaximal I.asIdeal |>.mp I.isPrime⟩
  invFun I := ⟨I.asIdeal, isPrime_iff_isMaximal I.asIdeal |>.mpr I.isMaximal⟩
/-
**IsArtinianRing.primeSpectrumEquivMaximalSpectrum_comp_asIdeal** 是 Mathlib 中的一个
引理，位于命名空间 `IsArtinianRing`。
形式化陈述：primeSpectrumEquivMaximalSpectrum_comp_asIdeal : MaximalSpectrum.asIdeal ∘
 primeSpectrumEquivMaximalSpectrum = PrimeSpectrum.asIdeal (R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma primeSpectrumEquivMaximalSpectrum_comp_asIdeal :
    MaximalSpectrum.asIdeal ∘ primeSpectrumEquivMaximalSpectrum =
      PrimeSpectrum.asIdeal (R := R) := rfl
/-
**IsArtinianRing.primeSpectrumEquivMaximalSpectrum_symm_comp_asIdeal** 是 Mathlib
 中的一个引理，位于命名空间 `IsArtinianRing`。
形式化陈述：primeSpectrumEquivMaximalSpectrum_symm_comp_asIdeal : PrimeSpectrum.asIdea
l ∘ primeSpectrumEquivMaximalSpectrum.symm = MaximalSpectrum.asIdeal (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma primeSpectrumEquivMaximalSpectrum_symm_comp_asIdeal :
    PrimeSpectrum.asIdeal ∘ primeSpectrumEquivMaximalSpectrum.symm =
      MaximalSpectrum.asIdeal (R := R) := rfl
/-
**IsArtinianRing.primeSpectrum_asIdeal_range_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsArt
inianRing`。
形式化陈述：primeSpectrum_asIdeal_range_eq : range PrimeSpectrum.asIdeal = (range <| M
aximalSpectrum.asIdeal (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrimeSpectrum.range_asIdeal`：range_asIdeal : Set.range PrimeSpectrum.asI
deal = {J : Ideal R | J.IsPrime}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MaximalSpectrum.range_asIdeal`：range_asIdeal : Set.range MaximalSpectrum
.asIdeal = {J : Ideal R | J.IsMaximal}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma primeSpectrum_asIdeal_range_eq :
    range PrimeSpectrum.asIdeal = (range <| MaximalSpectrum.asIdeal (R := R)) := by
  simp only [PrimeSpectrum.range_asIdeal, MaximalSpectrum.range_asIdeal,
    isPrime_iff_isMaximal]

variable (R)
/-
**IsArtinianRing.nilradical_pow_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinianRin
g`。
形式化陈述：nilradical_pow_eq_iInf (n : Nat) : nilradical R ^ n = iInf fun I : Maximal
Spectrum R => I.1 ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinianRing.instFiniteMaximalSpectrum`：∀ (R : Type u_1) [inst : CommS
emiring R] [IsArtinianRing R], Finite (MaximalSpectrum R)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {f
 : β → α}, ⨅ x ∈ Set.univ, f x = ⨅ x, f x
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `PrimeSpectrum.nilradical_eq_iInf`：nilradical_eq_iInf : nilradical R = iI
nf asIdeal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Ideal.prod_eq_iInf_of_pairwise_isCoprime`：prod_eq_iInf_of_pairwise_isCop
rime {s : Finset ι} {J : ι -> Ideal R} (hp : (s : Set ι).Pairwise (IsCoprime on 
J)) : ∏ i in s, J i = ⨅ i in s…
· 使用定理 `IsCoprime.pow`：IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x ^ m) (y 
^ n)
· 使用定理 `MaximalSpectrum.isCoprime_of_ne`：isCoprime_of_ne {I J : MaximalSpectrum 
R} (h : I != J) : IsCoprime I.1 J.1
· 使用定理 `Finset.prod_pow`：prod_pow (s : Finset ι) (n : Nat) (f : ι -> M) : ∏ x in
 s, f x ^ n = (∏ x in s, f x) ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `IsArtinianRing.primeSpectrum_asIdeal_range_eq`：primeSpectrum_asIdeal_ran
ge_eq : range PrimeSpectrum.asIdeal = (range <| MaximalSpectrum.asIdeal (R
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}
· 使用定理 `sInf_singleton`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {a : 
α}, sInf {a} = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nilradical_pow_eq_iInf (n : ℕ) :
    nilradical R ^ n = iInf fun I : MaximalSpectrum R ↦ I.1 ^ n := by
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite (MaximalSpectrum R)
  rw [← iInf_univ, ← Finset.coe_univ, PrimeSpectrum.nilradical_eq_iInf]
  simp only [Finset.mem_coe]
  rw [← Ideal.prod_eq_iInf_of_pairwise_isCoprime fun I _ _ _ ↦ .pow ∘ I.isCoprime_of_ne,
    Finset.prod_pow, Ideal.prod_eq_iInf_of_pairwise_isCoprime fun I _ _ _ ↦ I.isCoprime_of_ne]
  simp [Finset.mem_univ, iInf, IsArtinianRing.primeSpectrum_asIdeal_range_eq]
/-
**IsArtinianRing.nilradical_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinianRing`。
形式化陈述：nilradical_eq_iInf : nilradical R = iInf MaximalSpectrum.asIdeal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsArtinianRing.nilradical_pow_eq_iInf`：nilradical_pow_eq_iInf (n : Nat) 
: nilradical R ^ n = iInf fun I : MaximalSpectrum R => I.1 ^ n
-/
theorem nilradical_eq_iInf : nilradical R = iInf MaximalSpectrum.asIdeal := by
  simpa using nilradical_pow_eq_iInf R 1
/-
**IsArtinianRing.setOfPred_isPrime_finite** 是 Mathlib 中的一个引理，位于命名空间 `IsArtinianR
ing`。
形式化陈述：setOfPred_isPrime_finite : {I : Ideal R | I.IsPrime}.Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `IsArtinianRing.setOfPred_isMaximal_finite`：setOfPred_isMaximal_finite : 
{I : Ideal R | I.IsMaximal}.Finite
-/
lemma setOfPred_isPrime_finite : {I : Ideal R | I.IsPrime}.Finite := by
  simpa only [isPrime_iff_isMaximal] using setOfPred_isMaximal_finite R

@[deprecated (since := "2026-07-09")] alias setOf_isPrime_finite := setOfPred_isPrime_finite
/-
**IsArtinianRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsArtinianRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Finite (PrimeSpectrum R) :=
  haveI : Finite {I : Ideal R // I.IsPrime} := (setOfPred_isPrime_finite R).to_subtype
  .of_equiv _ (PrimeSpectrum.equivSubtype _).symm.toEquiv

/-- A temporary field instance on the quotients by maximal ideals. -/
/-
**IsArtinianRing.fieldOfSubtypeIsMaximal** 是 Mathlib 中的一个定义，位于命名空间 `IsArtinianRi
ng`。
形式化陈述：(R : Type u_1) → [inst : CommRing R] → (I : MaximalSpectrum R) → Field (R 
⧸ I.asIdeal)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A temporary field instance on the quotients by maximal ideals.
-/
@[instance_reducible, local instance] noncomputable def fieldOfSubtypeIsMaximal
    (I : MaximalSpectrum R) : Field (R ⧸ I.asIdeal) :=
  Ideal.Quotient.field I.asIdeal

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient of a commutative Artinian ring by its nilradical is isomorphic to
a finite product of fields, namely the quotients by the maximal ideals. -/
@[simps!]
/-
**IsArtinianRing.quotNilradicalEquivPi** 是 Mathlib 中的一个定义，位于命名空间 `IsArtinianRing
`。
形式化陈述：quotNilradicalEquivPi : (R ⧸ nilradical R) ≃ₐ[R] forall I : MaximalSpectru
m R, R ⧸ I.asIdeal
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinianRing.nilradical_eq_iInf`：nilradical_eq_iInf : nilradical R = i
Inf MaximalSpectrum.asIdeal

--- 原说明 ---
The quotient of a commutative Artinian ring by its nilradical is isomorphic to
a finite product of fields, namely the quotients by the maximal ideals.
-/
noncomputable def quotNilradicalEquivPi :
    (R ⧸ nilradical R) ≃ₐ[R] ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal :=
  (Ideal.quotientEquivAlgOfEq R (nilradical_eq_iInf R)).trans
    { __ := Ideal.quotientInfRingEquivPiQuotient _ fun I _ ↦ I.isCoprime_of_ne
      commutes' _ := rfl}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient of a commutative Artinian ring by a power of its nilradical is isomorphic to
a finite product of local rings, namely the quotients by the powers of the maximal ideals. -/
@[simps!]
/-
**IsArtinianRing.quotNilradicalPowEquivPi** 是 Mathlib 中的一个定义，位于命名空间 `IsArtinianR
ing`。
形式化陈述：quotNilradicalPowEquivPi (n : Nat) : (R ⧸ nilradical R ^ n) ≃ₐ[R] forall I
 : MaximalSpectrum R, R ⧸ I.asIdeal ^ n
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinianRing.nilradical_pow_eq_iInf`：nilradical_pow_eq_iInf (n : Nat) 
: nilradical R ^ n = iInf fun I : MaximalSpectrum R => I.1 ^ n

--- 原说明 ---
The quotient of a commutative Artinian ring by a power of its nilradical is isom
orphic to
a finite product of local rings, namely the quotients by the powers of the maxim
al ideals.
-/
noncomputable def quotNilradicalPowEquivPi (n : ℕ) :
    (R ⧸ nilradical R ^ n) ≃ₐ[R] ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal ^ n :=
  (Ideal.quotientEquivAlgOfEq R (nilradical_pow_eq_iInf R n)).trans
    { __ := Ideal.quotientInfRingEquivPiQuotient _ fun I _ ↦ .pow ∘ I.isCoprime_of_ne
      commutes' _ := rfl}

/-- A reduced commutative Artinian ring is isomorphic to a finite product of fields,
namely the quotients by the maximal ideals. -/
/-
**IsArtinianRing.equivPi** 是 Mathlib 中的一个定义，位于命名空间 `IsArtinianRing`。
形式化陈述：equivPi [IsReduced R] : R ≃ₐ[R] forall I : MaximalSpectrum R, R ⧸ I.asIdea
l
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A reduced commutative Artinian ring is isomorphic to a finite product of fields,
namely the quotients by the maximal ideals.
-/
noncomputable def equivPi [IsReduced R] : R ≃ₐ[R] ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal :=
  .trans (.symm <| .quotientBot R R) <| .trans
    (Ideal.quotientEquivAlgOfEq R (nilradical_eq_zero R).symm) (quotNilradicalEquivPi R)

@[simp]
/-
**IsArtinianRing.equivPi_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsArtinianRing`。
形式化陈述：equivPi_apply [IsReduced R] (x : R) (m : MaximalSpectrum R) : equivPi R x 
m = x
参数：x : R；m : MaximalSpectrum R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivPi_apply [IsReduced R] (x : R) (m : MaximalSpectrum R) : equivPi R x m = x :=
  rfl
/-
**IsArtinianRing.isSemisimpleRing_of_isReduced** 是 Mathlib 中的一个定理，位于命名空间 `IsArti
nianRing`。
形式化陈述：isSemisimpleRing_of_isReduced [IsReduced R] : IsSemisimpleRing R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.isSemisimpleRing`：RingEquiv.isSemisimpleRing (e : R ≃+* S) [Is
SemisimpleRing R] : IsSemisimpleRing S where __
· 使用定理 `instIsSemisimpleRingForallOfFinite`：∀ {ι : Type u_7} [Finite ι] (R : ι →
 Type u_6) [inst : (i : ι) → Ring (R i)] [∀ (i : ι), IsSemisimpleRing (R i)],   
IsSemisimpleRing ((i : ι…
· 使用定理 `IsArtinianRing.instFiniteMaximalSpectrum`：∀ (R : Type u_1) [inst : CommS
emiring R] [IsArtinianRing R], Finite (MaximalSpectrum R)
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
-/
theorem isSemisimpleRing_of_isReduced [IsReduced R] : IsSemisimpleRing R :=
  (equivPi R).symm.isSemisimpleRing

end CommRing

section Ring

variable {R : Type*} [Ring R] [IsArtinianRing R]

/-
**IsArtinianRing.isSemisimpleRing_iff_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `IsArti
nianRing`。
形式化陈述：isSemisimpleRing_iff_jacobson : IsSemisimpleRing R ↔ Ring.jacobson R = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinian.isSemisimpleModule_iff_jacobson`：IsArtinian.isSemisimpleModul
e_iff_jacobson [IsArtinian R M] : IsSemisimpleModule R M ↔ Module.jacobson R M =
 ⊥
-/
theorem isSemisimpleRing_iff_jacobson : IsSemisimpleRing R ↔ Ring.jacobson R = ⊥ :=
  IsArtinian.isSemisimpleModule_iff_jacobson R R
/-
**IsArtinianRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsArtinianRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSemiprimaryRing R where
  isSemisimpleRing :=
    IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr (Ring.jacobson_quotient_jacobson R)
  isNilpotent := by
    let Jac := Ring.jacobson R
    have ⟨n, hn⟩ := IsArtinian.monotone_stabilizes ⟨(Jac ^ ·), @Ideal.pow_le_pow_right _ _ _⟩
    have hn : Jac * Jac ^ n = Jac ^ n := by
      rw [← Ideal.IsTwoSided.pow_succ]; exact (hn _ n.le_succ).symm
    use n; by_contra ne
    have ⟨N, ⟨eq, ne⟩, min⟩ := wellFounded_lt.has_min {N | Jac * N = N ∧ N ≠ ⊥} ⟨_, hn, ne⟩
    have : Jac ^ n * N = N := n.rec (by rw [Jac.pow_zero, N.one_mul])
      fun n hn ↦ by rwa [Jac.pow_succ, mul_assoc, eq]
    let I x := Submodule.map (LinearMap.toSpanSingleton R R x) (Jac ^ n)
    have hI x : I x ≤ Ideal.span {x} := by
      rw [Ideal.span, LinearMap.span_singleton_eq_range]; exact LinearMap.map_le_range
    have ⟨x, hx⟩ : ∃ x ∈ N, I x ≠ ⊥ := by
      contrapose! ne
      rw [← this, ← le_bot_iff, Ideal.mul_le]
      refine fun ri hi rn hn ↦ ?_
      rw [← ne rn hn]
      exact ⟨ri, hi, rfl⟩
    rw [← Ideal.span_singleton_le_iff_mem] at hx
    have : I x = N := by
      refine ((hI x).trans hx.1).eq_of_not_lt (min _ ⟨?_, hx.2⟩)
      rw [← smul_eq_mul, ← Submodule.map_smul'', smul_eq_mul, hn]
    have : Ideal.span {x} = N := le_antisymm hx.1 (this.symm.trans_le <| hI x)
    refine (this ▸ ne) ((Submodule.fg_span <| Set.finite_singleton x).eq_bot_of_le_jacobson_smul ?_)
    rw [← Ideal.span, this, smul_eq_mul, eq]

end Ring

end IsArtinianRing

