/-
Copyright (c) 2025 Jinzhao Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Pan
-/
module

public import Mathlib.Order.RelSeries
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!

# Finitely generated module over Noetherian ring have finitely many associated primes.

In this file we proved that any finitely generated module over a Noetherian ring have finitely many
associated primes.

## Main results

* `IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime`: If `A` is a Noetherian ring
  and `M` is a finitely generated `A`-module, then there exists a chain of submodules
  `0 = M₀ ≤ M₁ ≤ M₂ ≤ ... ≤ Mₙ = M` of `M`, such that for each `0 ≤ i < n`,
  `Mᵢ₊₁ / Mᵢ` is isomorphic to `A / pᵢ` for some prime ideal `pᵢ` of `A`.

* `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`: If a property on
  finitely generated modules over a Noetherian ring satisfies that:

  - it holds for zero module,
  - it holds for any module isomorphic to some `A ⧸ p` where `p` is a prime ideal of `A`,
  - it is stable by short exact sequences,

  then the property holds for every finitely generated modules.

* `associatedPrimes.finite`: There are only finitely many associated primes of a
  finitely generated module over a Noetherian ring.

-/

@[expose] public section

universe u v

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- A `Prop` asserting that two submodules `N₁, N₂` satisfy `N₁ ≤ N₂` and
`N₂ / N₁` is isomorphic to `A / p` for some prime ideal `p` of `A`. -/
/-
**Submodule.IsQuotientEquivQuotientPrime** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.IsQuotientEquivQuotientPrime (N₁ N₂ : Submodule A M)
参数：N₁ N₂ : Submodule A M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Prop` asserting that two submodules `N₁, N₂` satisfy `N₁ ≤ N₂` and
`N₂ / N₁` is isomorphic to `A / p` for some prime ideal `p` of `A`.
-/
def Submodule.IsQuotientEquivQuotientPrime (N₁ N₂ : Submodule A M) :=
  N₁ ≤ N₂ ∧ ∃ (p : PrimeSpectrum A), Nonempty ((↥N₂ ⧸ N₁.submoduleOf N₂) ≃ₗ[A] A ⧸ p.1)

set_option backward.isDefEq.respectTransparency false in
open LinearMap in
/-
**Submodule.isQuotientEquivQuotientPrime_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.isQuotientEquivQuotientPrime_iff {N₁ N₂ : Submodule A M} : N₁.Is
QuotientEquivQuotientPrime N₂ ↔ exists x, Ideal.IsPrime ((⊥ : Submodule A (M ⧸ N
₁)).colon {N₁.mkQ x}) ∧ N₂ = N₁ ⊔ span A {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Submodule.ker_liftQ_eq_bot`：ker_liftQ_eq_bot (f : M ->ₛₗ[τ₁₂] M₂) (h) (h
' : ker f <= p) : ker (p.liftQ f h) = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `LinearMap.range.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u
_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCo
mmMonoid M] [ins…
· 使用定理 `Submodule.mapQ.eq_1`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [in
st_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {R₂ : 
Type u_3}…
· 使用定理 `Submodule.range_liftQ`：range_liftQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ
₁₂] M₂) (h) : range (p.liftQ f h) = range f
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
（共 62 条，此处仅展示前 30 条）
-/
theorem Submodule.isQuotientEquivQuotientPrime_iff {N₁ N₂ : Submodule A M} :
    N₁.IsQuotientEquivQuotientPrime N₂ ↔
      ∃ x, Ideal.IsPrime ((⊥ : Submodule A (M ⧸ N₁)).colon {N₁.mkQ x}) ∧ N₂ = N₁ ⊔ span A {x} := by
  let f := mapQ (N₁.submoduleOf N₂) N₁ N₂.subtype le_rfl
  have hf₁ : ker f = ⊥ := ker_liftQ_eq_bot _ _ _ (by simp [ker_comp, submoduleOf])
  have hf₂ : range f = N₂.map N₁.mkQ := by simp [f, mapQ, range_liftQ, range_comp]
  refine ⟨fun ⟨h, p, ⟨e⟩⟩ ↦ ?_, fun ⟨x, hx, hx'⟩ ↦ ⟨le_sup_left.trans_eq hx'.symm, ⟨_, hx⟩, ?_⟩⟩
  · obtain ⟨⟨x, hx⟩, hx'⟩ := Submodule.mkQ_surjective _ (e.symm 1)
    have hx'' : N₁.mkQ x = f (e.symm 1) := by simp [f, ← hx']
    refine ⟨x, ?_, ?_⟩
    · convert! p.2
      ext r
      simp [hx'', ← map_smul, Algebra.smul_def, show f _ = 0 ↔ _ from congr(_ ∈ $hf₁),
        Ideal.Quotient.eq_zero_iff_mem]
    · refine le_antisymm ?_ (sup_le h ((span_singleton_le_iff_mem _ _).mpr hx))
      have : (span A {x}).map N₁.mkQ = ((span A {1}).map e.symm.toLinearMap).map f := by
        simp only [map_span, Set.image_singleton, hx'', LinearEquiv.coe_coe]
      rw [← N₁.ker_mkQ, sup_comm, ← comap_map_eq, ← map_le_iff_le_comap, this]
      simp [hf₂, Ideal.Quotient.span_singleton_one]
  · have hxN₂ : x ∈ N₂ := (le_sup_right.trans_eq hx'.symm) (mem_span_singleton_self x)
    refine ⟨.symm (.ofBijective (Submodule.mapQ _ _ (toSpanSingleton A _ ⟨x, hxN₂⟩) ?_) ⟨?_, ?_⟩)⟩
    · simp [SetLike.le_def, ← Quotient.mk_smul, submoduleOf]
    · refine ker_eq_bot.mp (ker_liftQ_eq_bot _ _ _ ?_)
      simp [← Quotient.mk_smul, SetLike.le_def, submoduleOf]
    · rw [mapQ, ← range_eq_top, range_liftQ, range_comp]
      have := congr($(hx').submoduleOf N₂)
      rw [submoduleOf_self, submoduleOf_sup_of_le (by simp_all) (by simp_all),
        submoduleOf_span_singleton_of_mem _ hxN₂] at this
      simpa [← span_singleton_eq_range, LinearMap.range_toSpanSingleton] using this.symm

variable (A M) [IsNoetherianRing A] [Module.Finite A M]

/-- If `A` is a Noetherian ring and `M` is a finitely generated `A`-module, then there exists
a chain of submodules `0 = M₀ ≤ M₁ ≤ M₂ ≤ ... ≤ Mₙ = M` of `M`, such that for each `0 ≤ i < n`,
`Mᵢ₊₁ / Mᵢ` is isomorphic to `A / pᵢ` for some prime ideal `pᵢ` of `A`. -/
@[stacks 00L0]
/-
**IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime : exists s 
: RelSeries {(N₁, N₂) | Submodule.IsQuotientEquivQuotientPrime (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedGT.induction_top`：WellFoundedGT.induction_top [Preorder α] [W
ellFoundedGT α] [OrderTop α] {P : α -> Prop} (hexists : exists M, P M) (hind : f
orall N != ⊤, P N…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.nontrivial_iff`：∀ {R : Type u_1} {M : Type u_2} [inst
 : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submodu
le R M}, Nontrivial (M …
· 使用定理 `associatedPrimes.nonempty`：associatedPrimes.nonempty [IsNoetherianRing R
] [Nontrivial M] : (associatedPrimes R M).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isAssociatedPrime_iff`：isAssociatedPrime_iff [IsNoetherianRing R] : IsAs
sociatedPrime I M ↔ I.IsPrime ∧ exists x : M, I = colon ⊥ {x}
· 使用定理 `AssociatedPrimes.mem_iff`：AssociatedPrimes.mem_iff : I in associatedPrim
es R M ↔ IsAssociatedPrime I M
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.isQuotientEquivQuotientPrime_iff`：Submodule.isQuotientEquivQuo
tientPrime_iff {N₁ N₂ : Submodule A M} : N₁.IsQuotientEquivQuotientPrime N₂ ↔ ex
ists x, Ideal.IsPrime ((⊥ : Subm…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RelSeries.snoc.congr_simp`：∀ {α : Type u_1} {r : SetRel α α} (p p_1 : Re
lSeries r) (e_p : p = p_1) (newLast newLast_1 : α)   (e_newLast : newLast = newL
ast_1) (rel : (…
· 使用定理 `RelSeries.last_snoc`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r)
 (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).last = newL
ast
· 使用定理 `RelSeries.head_snoc`：∀ {α : Type u_1} {r : SetRel α α} (p : RelSeries r)
 (newLast : α) (rel : (p.last, newLast) ∈ r),   (p.snoc newLast rel).head = p.he
ad

--- 原说明 ---
If `A` is a Noetherian ring and `M` is a finitely generated `A`-module, then the
re exists
a chain of submodules `0 = M₀ ≤ M₁ ≤ M₂ ≤ ... ≤ Mₙ = M` of `M`, such that for ea
ch `0 ≤ i < n`,
`Mᵢ₊₁ / Mᵢ` is isomorphic to `A / pᵢ` for some prime ideal `pᵢ` of `A`.
-/
theorem IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime :
    ∃ s : RelSeries {(N₁, N₂) | Submodule.IsQuotientEquivQuotientPrime (A := A) (M := M) N₁ N₂},
      s.head = ⊥ ∧ s.last = ⊤ := by
  refine WellFoundedGT.induction_top ⟨⊥, .singleton _ ⊥, rfl, rfl⟩ ?_
  rintro N hN ⟨s, hs₁, hs₂⟩
  have := Submodule.Quotient.nontrivial_iff.mpr hN
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty A (M ⧸ N)
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp
  obtain ⟨hp, x, rfl⟩ := hp
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  have hxN : x ∉ N := fun h ↦ hp.ne_top (by rw [show N.mkQ x = 0 by simpa]; simp)
  have := Submodule.isQuotientEquivQuotientPrime_iff.mpr ⟨x, hp, rfl⟩
  refine ⟨_, by simpa [hs₂], s.snoc _ (hs₂ ▸ this), by simpa, rfl⟩

/-- If a property on finitely generated modules over a Noetherian ring satisfies that:

- it holds for zero module (it's formalized as it holds for any module which is subsingleton),
- it holds for `A ⧸ p` for every prime ideal `p` of `A` (to avoid universe problem,
  it's formalized as it holds for any module isomorphic to `A ⧸ p`),
- it is stable by short exact sequences,

then the property holds for every finitely generated modules.

NOTE: This should be the induction principle for `M`, but due to the bug
https://github.com/leanprover/lean4/issues/4246
currently it is induction for `Module.Finite A M`. -/
@[elab_as_elim]
/-
**IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime ⦃M : Type v⦄ [A
ddCommGroup M] [Module A M] (_ : Module.Finite A M) {motive : (N : Type v) -> [A
ddCommGroup N] -> [Module A N] -> [Module.Finite A N] -> Prop} (subsingleton : (
N : Type v) -> [AddCommGroup N] -> [Module A N] -> [Module.Finite A N] -> [Subsi
ngleton N] -> motive N) (quotient : (N : Type v) -> [AddCommGroup N] -> [Module 
A N] -> [Module.Finite A N] -> (p : PrimeSpectrum A) -> (N ≃ₗ[A] A ⧸ p.1) -> mot
ive N) (exact : (N₁ : Type
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Function.surjective_to_subsingleton`：surjective_to_subsingleton [na : No
nempty α] [Subsingleton β] (f : α -> β) : Surjective f
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.exact_zero_iff_surjective`：exact_zero_iff_surjective {M N : Ty
pe*} (P : Type*) [AddCommGroup M] [AddCommGroup N] [AddCommMonoid P] [Module R N
] [Module R M] [Module R …
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime`：IsNoethe
rianRing.exists_relSeries_isQuotientEquivQuotientPrime : exists s : RelSeries {(
N₁, N₂) | Submodule.IsQuotientEquivQuotientPrime (A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_lt_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [A
ddRightStrictMono α] [AddRightReflectLT α] (a : α) {b c : α},   b + a < c + a ↔ 
b < c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用引理 `LinearMap.exact_subtype_mkQ`：exact_subtype_mkQ (Q : Submodule R N) : Exa
ct (Submodule.subtype Q) (Submodule.mkQ Q)

--- 原说明 ---
If a property on finitely generated modules over a Noetherian ring satisfies tha
t:

- it holds for zero module (it's formalized as it holds for any module which is 
subsingleton),
- it holds for `A ⧸ p` for every prime ideal `p` of `A` (to avoid universe probl
em,
  it's formalized as it holds for any module isomorphic to `A ⧸ p`),
- it is stable by short exact sequences,

then the property holds for every finitely generated modules.

NOTE: This should be the induction principle for `M`, but due to the bug
https://github.com/leanprover/lean4/issues/4246
currently it is induction for `Module.Finite A M`.
-/
theorem IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
    ⦃M : Type v⦄ [AddCommGroup M] [Module A M] (_ : Module.Finite A M)
    {motive : (N : Type v) → [AddCommGroup N] → [Module A N] → [Module.Finite A N] → Prop}
    (subsingleton : (N : Type v) → [AddCommGroup N] → [Module A N] → [Module.Finite A N] →
      [Subsingleton N] → motive N)
    (quotient : (N : Type v) → [AddCommGroup N] → [Module A N] → [Module.Finite A N] →
      (p : PrimeSpectrum A) → (N ≃ₗ[A] A ⧸ p.1) → motive N)
    (exact : (N₁ : Type v) → [AddCommGroup N₁] → [Module A N₁] → [Module.Finite A N₁] →
      (N₂ : Type v) → [AddCommGroup N₂] → [Module A N₂] → [Module.Finite A N₂] →
      (N₃ : Type v) → [AddCommGroup N₃] → [Module A N₃] → [Module.Finite A N₃] →
      (f : N₁ →ₗ[A] N₂) → (g : N₂ →ₗ[A] N₃) →
      Function.Injective f → Function.Surjective g → Function.Exact f g →
      motive N₁ → motive N₃ → motive N₂) : motive M := by
  have equiv (N₁ : Type v) [AddCommGroup N₁] [Module A N₁] [Module.Finite A N₁]
      (N₂ : Type v) [AddCommGroup N₂] [Module A N₂] [Module.Finite A N₂]
      (f : N₁ ≃ₗ[A] N₂) (h : motive N₁) : motive N₂ :=
    exact N₁ N₂ PUnit.{v + 1} f 0 f.injective (Function.surjective_to_subsingleton _)
      ((f.exact_zero_iff_surjective _).2 f.surjective) h (subsingleton _)
  obtain ⟨s, hs1, hs2⟩ := IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime A M
  suffices H : ∀ n, (h : n < s.length + 1) → motive (s ⟨n, h⟩) by
    replace H : motive s.last := H s.length s.length.lt_add_one
    rw [hs2] at H
    exact equiv _ _ Submodule.topEquiv H
  intro n h
  induction n with
  | zero =>
    change motive s.head
    rw [hs1]
    exact subsingleton _
  | succ n ih =>
    specialize ih (n.lt_add_one.trans h)
    obtain ⟨hle, p, ⟨f⟩⟩ := s.step ⟨n, (add_lt_add_iff_right _).1 h⟩
    replace ih := equiv _ _ (Submodule.submoduleOfEquivOfLe hle).symm ih
    exact exact _ _ _ _ _ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ _) ih (quotient _ p f)

/-- There are only finitely many associated primes of a finitely generated module
over a Noetherian ring. -/
@[stacks 00LC]
/-
**associatedPrimes.finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：associatedPrimes.finite : (associatedPrimes A M).Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`：IsNoetherian
Ring.induction_on_isQuotientEquivQuotientPrime ⦃M : Type v⦄ [AddCommGroup M] [Mo
dule A M] (_ : Module.Finite A M) {motive : (N :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `associatedPrimes.eq_empty_of_subsingleton`：associatedPrimes.eq_empty_of_
subsingleton [Subsingleton M] : associatedPrimes R M = ∅
· 使用定理 `associatedPrimes.eq_singleton_of_isPrimary`：associatedPrimes.eq_singleto
n_of_isPrimary [IsNoetherianRing R] (hI : I.IsPrimary) : associatedPrimes R (R ⧸
 I) = {I.radical}
· 使用定理 `Ideal.IsPrime.isPrimary`：∀ {R : Type u_1} [inst : CommSemiring R] {I : I
deal R}, I.IsPrime → I.IsPrimary
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `LinearEquiv.AssociatedPrimes.eq`：LinearEquiv.AssociatedPrimes.eq (l : M 
≃ₗ[R] M') : associatedPrimes R M = associatedPrimes R M'
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `associatedPrimes.subset_union_of_exact`：subset_union_of_exact (hf : Func
tion.Injective f) (hfg : Function.Exact f g) : associatedPrimes R M' subseteq as
sociatedPrimes R M union ass…

--- 原说明 ---
There are only finitely many associated primes of a finitely generated module
over a Noetherian ring.
-/
theorem associatedPrimes.finite : (associatedPrimes A M).Finite := by
  induction ‹Module.Finite A M› using
    IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A with
  | subsingleton N => simp [associatedPrimes.eq_empty_of_subsingleton]
  | quotient N p f =>
    have := associatedPrimes.eq_singleton_of_isPrimary p.2.isPrimary
    simp [LinearEquiv.AssociatedPrimes.eq f, this]
  | exact N₁ N₂ N₃ f g hf _ hfg h₁ h₃ =>
    exact (h₁.union h₃).subset (associatedPrimes.subset_union_of_exact hf hfg)

/-- Every maximal ideal of a commutative Noetherian total ring of fractions `A` is
an associated prime of the `A`-module `A`. -/
/-
**Ideal.IsMaximal.mem_associatedPrimes_of_isFractionRing** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：Ideal.IsMaximal.mem_associatedPrimes_of_isFractionRing [IsFractionRing A A
] (I : Ideal A) [hI : I.IsMaximal] : I in associatedPrimes A A
参数：I : Ideal A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `associatedPrimes.finite`：associatedPrimes.finite : (associatedPrimes A M
).Finite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Ideal.subset_union_prime_finite`：subset_union_prime_finite {R ι : Type*}
 [CommRing R] {s : Set ι} (hs : s.Finite) {f : ι -> Ideal R} (a b : ι) (hp : for
all i in s, i != a ->…
· 使用定理 `IsAssociatedPrime.isPrime`：IsAssociatedPrime.isPrime (h : IsAssociatedPr
ime I M) : I.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `biUnion_associatedPrimes_eq_compl_nonZeroDivisors`：biUnion_associatedPri
mes_eq_compl_nonZeroDivisors [IsNoetherianRing R] : ⋃ p in associatedPrimes R R,
 p = (nonZeroDivisors R : Set R)ᶜ
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `IsFractionRing.self_iff_nonZeroDivisors_le_isUnit`：self_iff_nonZeroDivis
ors_le_isUnit : IsFractionRing R R ↔ R⁰ <= IsUnit.submonoid R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Every maximal ideal of a commutative Noetherian total ring of fractions `A` is
an associated prime of the `A`-module `A`.
-/
theorem Ideal.IsMaximal.mem_associatedPrimes_of_isFractionRing [IsFractionRing A A]
    (I : Ideal A) [hI : I.IsMaximal] : I ∈ associatedPrimes A A :=
  have fin := associatedPrimes.finite A A
  have ⟨P, hP⟩ := (I.subset_union_prime_finite fin (f := id) 0 0 fun _ h _ _ ↦ h.isPrime).1 <| by
    simp_rw [id, biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
    exact fun x hx h ↦ hI.ne_top <| I.eq_top_of_isUnit_mem hx
      (IsFractionRing.self_iff_nonZeroDivisors_le_isUnit.mp ‹_› h)
  hI.eq_of_le hP.1.isPrime.ne_top hP.2 ▸ hP.1

/-- A commutative Noetherian total ring of fractions is semilocal. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commutative Noetherian total ring of fractions is semilocal.
-/
instance [IsFractionRing A A] : Finite (MaximalSpectrum A) :=
  (MaximalSpectrum.equivSubtype A).finite_iff.mpr <| Set.finite_coe_iff.mpr <|
    (associatedPrimes.finite A A).subset fun _ ↦ (·.mem_associatedPrimes_of_isFractionRing)

variable {A}

/-- An ideal consisting of zero divisors in a commutative Noetherian ring is annihilated by
some nonzero element. This is not true in general for finitely generated modules in commutative
rings, see https://math.stackexchange.com/q/1189814 and http://dx.doi.org/10.2140/pjm.1979.83.375
(keywords: Property (A), Quentel's Condition (C)).

It is also not true that every finitely generated module over every commutative Noetherian ring
is annihilated by some nonzero element if each element is annihilated by some nonzero element,
see https://math.stackexchange.com/a/3187153. -/
/-
**Ideal.bot_lt_annihilator_of_disjoint_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Ideal.bot_lt_annihilator_of_disjoint_nonZeroDivisors {I : Ideal A} (h : Di
sjoint (I : Set A) (nonZeroDivisors A)) : ⊥ < Module.annihilator A I
参数：h : Disjoint (I : Set A) (nonZeroDivisors A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Ideal.subset_union_prime_finite`：subset_union_prime_finite {R ι : Type*}
 [CommRing R] {s : Set ι} (hs : s.Finite) {f : ι -> Ideal R} (a b : ι) (hp : for
all i in s, i != a ->…
· 使用定理 `associatedPrimes.finite`：associatedPrimes.finite : (associatedPrimes A M
).Finite
· 使用定理 `Submodule.IsAssociatedPrime.toIsPrime`：∀ {R : Type u_1} {M : Type u_2} [
inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]  
 {N : Submodule R M} {I : I…
· 使用定理 `Disjoint.subset_compl_right`：∀ {α : Type u_1} {s t : Set α}, Disjoint s 
t → s ⊆ tᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `biUnion_associatedPrimes_eq_compl_nonZeroDivisors`：biUnion_associatedPri
mes_eq_compl_nonZeroDivisors [IsNoetherianRing R] : ⋃ p in associatedPrimes R R,
 p = (nonZeroDivisors R : Set R)ᶜ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isAssociatedPrime_iff`：isAssociatedPrime_iff [IsNoetherianRing R] : IsAs
sociatedPrime I M ↔ I.IsPrime ∧ exists x : M, I = colon ⊥ {x}
· 使用定理 `AssociatedPrimes.mem_iff`：AssociatedPrimes.mem_iff : I in associatedPrim
es R M ↔ IsAssociatedPrime I M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.lt_iff_le_and_exists`：lt_iff_le_and_exists : p < q ↔ p <= q ∧ ex
ists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Submodule.mem_annihilator`：mem_annihilator {r} : r in N.annihilator ↔ fo
rall n in N, r • n = (0 : M)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
An ideal consisting of zero divisors in a commutative Noetherian ring is annihil
ated by
some nonzero element. This is not true in general for finitely generated modules
 in commutative
rings, see https://math.stackexchange.com/q/1189814 and http://dx.doi.org/10.214
0/pjm.1979.83.375
(keywords: Property (A), Quentel's Condition (C)).

It is also not true that every finitely generated module over every commutative 
Noetherian ring
is annihilated by some nonzero element if each element is annihilated by some no
nzero element,
see https://math.stackexchange.com/a/3187153.
-/
theorem Ideal.bot_lt_annihilator_of_disjoint_nonZeroDivisors {I : Ideal A}
    (h : Disjoint (I : Set A) (nonZeroDivisors A)) : ⊥ < Module.annihilator A I := by
  obtain ⟨P, h, hP⟩ : ∃ P ∈ associatedPrimes A A, I ≤ P :=
    (I.subset_union_prime_finite (associatedPrimes.finite ..) (f := id) 0 0 fun _ h _ _ ↦ h.1).1 <|
    biUnion_associatedPrimes_eq_compl_nonZeroDivisors A ▸ h.subset_compl_right
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at h
  obtain ⟨prime, x, rfl⟩ := h
  exact SetLike.lt_iff_le_and_exists.mpr ⟨bot_le, x, Submodule.mem_annihilator.mpr <| by
    simpa only [smul_eq_mul, mul_comm x, SetLike.le_def, Submodule.mem_colon_singleton] using! hP,
      fun h : x = 0 ↦ prime.ne_top <| by simp [h]⟩
/-
**Ideal.nonempty_inter_nonZeroDivisors_of_faithfulSMul** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Ideal.nonempty_inter_nonZeroDivisors_of_faithfulSMul {I : Ideal A} [Faithf
ulSMul A I] : ((I : Set A) inter nonZeroDivisors A).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Ideal.bot_lt_annihilator_of_disjoint_nonZeroDivisors`：Ideal.bot_lt_annih
ilator_of_disjoint_nonZeroDivisors {I : Ideal A} (h : Disjoint (I : Set A) (nonZ
eroDivisors A)) : ⊥ < Module.annihilator A…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.annihilator_eq_bot`：Module.annihilator_eq_bot {R M} [Ring R] [Add
CommGroup M] [Module R M] : Module.annihilator R M = ⊥ ↔ FaithfulSMul R M
-/
theorem Ideal.nonempty_inter_nonZeroDivisors_of_faithfulSMul {I : Ideal A} [FaithfulSMul A I] :
    ((I : Set A) ∩ nonZeroDivisors A).Nonempty := by
  by_contra!
  exact (bot_lt_annihilator_of_disjoint_nonZeroDivisors
    (Set.disjoint_iff_inter_eq_empty.mpr this)).ne' <| by rwa [Module.annihilator_eq_bot]
