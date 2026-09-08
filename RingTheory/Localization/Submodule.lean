/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.EssentialFiniteness

/-!
# Submodules in localizations of commutative rings

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section


variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]
variable [Algebra R S]

namespace IsLocalization

-- This was previously a `hasCoe` instance, but if `S = R` then this will loop.
-- It could be a `hasCoeT` instance, but we keep it explicit here to avoid slowing down
-- the rest of the library.
/-- Map from ideals of `R` to submodules of `S` induced by `f`. -/
/-
**IsLocalization.coeSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：coeSubmodule (I : Ideal R) : Submodule R S
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map from ideals of `R` to submodules of `S` induced by `f`.
-/
def coeSubmodule (I : Ideal R) : Submodule R S :=
  Submodule.map (Algebra.linearMap R S) I
/-
**IsLocalization.mem_coeSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：mem_coeSubmodule (I : Ideal R) {x : S} : x in coeSubmodule S I ↔ exists y 
: R, y in I ∧ algebraMap R S y = x
参数：I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coeSubmodule (I : Ideal R) {x : S} :
    x ∈ coeSubmodule S I ↔ ∃ y : R, y ∈ I ∧ algebraMap R S y = x :=
  Iff.rfl
/-
**IsLocalization.coeSubmodule_mono** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：coeSubmodule_mono {I J : Ideal R} (h : I <= J) : coeSubmodule S I <= coeSu
bmodule S J
参数：h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_mono`：map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M}
 : p <= p' -> map f p <= map f p'
-/
theorem coeSubmodule_mono {I J : Ideal R} (h : I ≤ J) : coeSubmodule S I ≤ coeSubmodule S J :=
  Submodule.map_mono h

@[simp]
/-
**IsLocalization.coeSubmodule_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：coeSubmodule_bot : coeSubmodule S (⊥ : Ideal R) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.coeSubmodule.eq_1`：∀ {R : Type u_1} [inst : CommSemiring 
R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (I : Ideal R)
,   IsLocalization.coe…
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
-/
theorem coeSubmodule_bot : coeSubmodule S (⊥ : Ideal R) = ⊥ := by
  rw [coeSubmodule, Submodule.map_bot]

@[simp]
/-
**IsLocalization.coeSubmodule_top** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：coeSubmodule_top : coeSubmodule S (⊤ : Ideal R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.coeSubmodule.eq_1`：∀ {R : Type u_1} [inst : CommSemiring 
R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (I : Ideal R)
,   IsLocalization.coe…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.one_eq_range`：one_eq_range : (1 : Submodule R A) = LinearMap.r
ange (Algebra.linearMap R A)
-/
theorem coeSubmodule_top : coeSubmodule S (⊤ : Ideal R) = 1 := by
  rw [coeSubmodule, Submodule.map_top, Submodule.one_eq_range]

@[simp]
/-
**IsLocalization.coeSubmodule_sup** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：coeSubmodule_sup (I J : Ideal R) : coeSubmodule S (I ⊔ J) = coeSubmodule S
 I ⊔ coeSubmodule S J
参数：I J : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_sup`：map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f
 p ⊔ map f p'
-/
theorem coeSubmodule_sup (I J : Ideal R) :
    coeSubmodule S (I ⊔ J) = coeSubmodule S I ⊔ coeSubmodule S J :=
  Submodule.map_sup _ _ _

@[simp]
/-
**IsLocalization.coeSubmodule_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：coeSubmodule_mul (I J : Ideal R) : coeSubmodule S (I * J) = coeSubmodule S
 I * coeSubmodule S J
参数：I J : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_mul`：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [
inst_1 : Semiring A] [inst_2 : Algebra R A] (M N : Submodule R A)   {A' : Type u
_1} [in…
-/
theorem coeSubmodule_mul (I J : Ideal R) :
    coeSubmodule S (I * J) = coeSubmodule S I * coeSubmodule S J :=
  Submodule.map_mul _ _ (Algebra.ofId R S)
/-
**IsLocalization.coeSubmodule_fg** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：coeSubmodule_fg (hS : Function.Injective (algebraMap R S)) (I : Ideal R) :
 Submodule.FG (coeSubmodule S I) ↔ Submodule.FG I
参数：hS : Function.Injective (algebraMap R S)；I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.fg_of_fg_map_injective`：fg_of_fg_map_injective (hf : Function.
Injective f) {N : Submodule R M} (hfn : (N.map f).FG) : N.FG
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
-/
theorem coeSubmodule_fg (hS : Function.Injective (algebraMap R S)) (I : Ideal R) :
    Submodule.FG (coeSubmodule S I) ↔ Submodule.FG I :=
  ⟨Submodule.fg_of_fg_map_injective _ hS, Submodule.FG.map _⟩

@[simp]
/-
**IsLocalization.coeSubmodule_span** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：coeSubmodule_span (s : Set R) : coeSubmodule S (Ideal.span s) = Submodule.
span R (algebraMap R S '' s)
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.coeSubmodule.eq_1`：∀ {R : Type u_1} [inst : CommSemiring 
R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (I : Ideal R)
,   IsLocalization.coe…
· 使用定理 `Ideal.span.eq_1`：∀ {α : Type u} [inst : Semiring α] (s : Set α), Ideal.s
pan s = Submodule.span α s
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
-/
theorem coeSubmodule_span (s : Set R) :
    coeSubmodule S (Ideal.span s) = Submodule.span R (algebraMap R S '' s) := by
  rw [IsLocalization.coeSubmodule, Ideal.span, Submodule.map_span]
  rfl
/-
**IsLocalization.coeSubmodule_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `IsLocali
zation`。
形式化陈述：coeSubmodule_span_singleton (x : R) : coeSubmodule S (Ideal.span {x}) = Su
bmodule.span R {(algebraMap R S) x}
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.coeSubmodule_span`：coeSubmodule_span (s : Set R) : coeSub
module S (Ideal.span s) = Submodule.span R (algebraMap R S '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
-/
theorem coeSubmodule_span_singleton (x : R) :
    coeSubmodule S (Ideal.span {x}) = Submodule.span R {(algebraMap R S) x} := by
  rw [coeSubmodule_span, Set.image_singleton]

variable [IsLocalization M S]

include M in
/-
**IsLocalization.isNoetherianRing** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：isNoetherianRing (h : IsNoetherianRing R) : IsNoetherianRing S
参数：h : IsNoetherianRing R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isNoetherianRing_iff`：isNoetherianRing_iff {R} [Semiring R] : IsNoetheri
anRing R ↔ IsNoetherian R R
· 使用定理 `isNoetherian_iff`：isNoetherian_iff : IsNoetherian R M ↔ WellFounded ((· 
> ·) : Submodule R M -> Submodule R M -> Prop)
· 使用定理 `OrderEmbedding.wellFounded`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β] (f : α ↪o β),   (WellFounded fun x1 x2 => x1 < x2)
 → WellFounded f…
-/
theorem isNoetherianRing (h : IsNoetherianRing R) : IsNoetherianRing S := by
  rw [isNoetherianRing_iff, isNoetherian_iff] at h ⊢
  exact OrderEmbedding.wellFounded (IsLocalization.orderEmbedding M S).dual h
/-
**IsLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R} [CommRing R] [IsNoetherianRing R] (S : Submonoid R) :
    IsNoetherianRing (Localization S) :=
  IsLocalization.isNoetherianRing S _ ‹_›
/-
**IsLocalization._root_.Algebra.EssFiniteType.isNoetherianRing** 是 Mathlib 中的一个引
理，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Algebra.EssFiniteType.isNoetherianRing
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [IsNoetherianRing R] : IsNoetherianRing S := by
  exact IsLocalization.isNoetherianRing (Algebra.EssFiniteType.submonoid R S) _
    (Algebra.FiniteType.isNoetherianRing R _)
section NonZeroDivisors

variable {R : Type*} [CommRing R] {M : Submonoid R}
  {S : Type*} [CommRing S] [Algebra R S] [IsLocalization M S]

@[gcongr, mono]
/-
**IsLocalization.coeSubmodule_le_coeSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `IsLocal
ization`。
形式化陈述：coeSubmodule_le_coeSubmodule (h : M <= nonZeroDivisors R) {I J : Ideal R} 
: coeSubmodule S I <= coeSubmodule S J ↔ I <= J
参数：h : M <= nonZeroDivisors R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_le_map_iff_of_injective`：map_le_map_iff_of_injective (p q 
: Submodule R M) : p.map f <= q.map f ↔ p <= q
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
-/
theorem coeSubmodule_le_coeSubmodule (h : M ≤ nonZeroDivisors R) {I J : Ideal R} :
    coeSubmodule S I ≤ coeSubmodule S J ↔ I ≤ J :=
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify the value of `f` here:
  Submodule.map_le_map_iff_of_injective (f := Algebra.linearMap R S) (IsLocalization.injective _ h)
    _ _

@[gcongr, mono]
/-
**IsLocalization.coeSubmodule_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizati
on`。
形式化陈述：coeSubmodule_strictMono (h : M <= nonZeroDivisors R) : StrictMono (coeSubm
odule S : Ideal R -> Submodule R S)
参数：h : M <= nonZeroDivisors R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_of_le_iff_le`：strictMono_of_le_iff_le [Preorder α] [Preorder 
β] {f : α -> β} (h : forall x y, x <= y ↔ f x <= f y) : StrictMono f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `IsLocalization.coeSubmodule_le_coeSubmodule`：coeSubmodule_le_coeSubmodul
e (h : M <= nonZeroDivisors R) {I J : Ideal R} : coeSubmodule S I <= coeSubmodul
e S J ↔ I <= J
-/
theorem coeSubmodule_strictMono (h : M ≤ nonZeroDivisors R) :
    StrictMono (coeSubmodule S : Ideal R → Submodule R S) :=
  strictMono_of_le_iff_le fun _ _ => (coeSubmodule_le_coeSubmodule h).symm

variable (S)
/-
**IsLocalization.coeSubmodule_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizatio
n`。
形式化陈述：coeSubmodule_injective (h : M <= nonZeroDivisors R) : Function.Injective (
coeSubmodule S : Ideal R -> Submodule R S)
参数：h : M <= nonZeroDivisors R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_eq_imp_le`：Function.Injective.of_eq_imp_le [Partia
lOrder α] {f : α -> β} (h : forall {x y}, f x = f y -> x <= y) : f.Injective
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.coeSubmodule_le_coeSubmodule`：coeSubmodule_le_coeSubmodul
e (h : M <= nonZeroDivisors R) {I J : Ideal R} : coeSubmodule S I <= coeSubmodul
e S J ↔ I <= J
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem coeSubmodule_injective (h : M ≤ nonZeroDivisors R) :
    Function.Injective (coeSubmodule S : Ideal R → Submodule R S) :=
  .of_eq_imp_le fun hl => (coeSubmodule_le_coeSubmodule h).mp hl.le
/-
**IsLocalization.coeSubmodule_isPrincipal** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizat
ion`。
形式化陈述：coeSubmodule_isPrincipal {I : Ideal R} (h : M <= nonZeroDivisors R) : (coe
Submodule S I).IsPrincipal ↔ I.IsPrincipal
参数：h : M <= nonZeroDivisors R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.mem_coeSubmodule`：mem_coeSubmodule (I : Ideal R) {x : S} 
: x in coeSubmodule S I ↔ exists y : R, y in I ∧ algebraMap R S y = x
· 使用定理 `IsLocalization.coeSubmodule_injective`：coeSubmodule_injective (h : M <= 
nonZeroDivisors R) : Function.Injective (coeSubmodule S : Ideal R -> Submodule R
 S)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `IsLocalization.coeSubmodule_span_singleton`：coeSubmodule_span_singleton 
(x : R) : coeSubmodule S (Ideal.span {x}) = Submodule.span R {(algebraMap R S) x
}
-/
theorem coeSubmodule_isPrincipal {I : Ideal R} (h : M ≤ nonZeroDivisors R) :
    (coeSubmodule S I).IsPrincipal ↔ I.IsPrincipal := by
  constructor <;> rintro ⟨⟨x, hx⟩⟩
  · have x_mem : x ∈ coeSubmodule S I := hx.symm ▸ Submodule.mem_span_singleton_self x
    obtain ⟨x, _, rfl⟩ := (mem_coeSubmodule _ _).mp x_mem
    refine ⟨⟨x, coeSubmodule_injective S h ?_⟩⟩
    rw [Ideal.submodule_span_eq, hx, coeSubmodule_span_singleton]
  · refine ⟨⟨algebraMap R S x, ?_⟩⟩
    rw [hx, Ideal.submodule_span_eq, coeSubmodule_span_singleton]

end NonZeroDivisors

variable {S}

/-
**IsLocalization.mem_span_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：mem_span_iff {N : Type*} [AddCommMonoid N] [Module R N] [Module S N] [IsSc
alarTower R S N] {x : N} {a : Set N} : x in Submodule.span S a ↔ exists y in Sub
module.span R a, exists z : M, x = mk' S 1 z • y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
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
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_smul`：algebraMap_smul [SMul R M] [IsScalarTower
 R A M] (r : R) (x : M) : algebraMap R A r • x = r • x
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsLocalization.mk'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsLocalization.mul_mk'_eq_mk'_of_mul`：∀ {R : Type u_1} [inst : CommSemir
ing R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Al
gebra R S] [inst_3 : IsLoc…
· 使用定理 `Submodule.span_subset_span`：span_subset_span : ↑(span R s) subseteq (spa
n S s : Set M)
-/
theorem mem_span_iff {N : Type*} [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
    {x : N} {a : Set N} :
    x ∈ Submodule.span S a ↔ ∃ y ∈ Submodule.span R a, ∃ z : M, x = mk' S 1 z • y := by
  constructor
  · intro h
    refine Submodule.span_induction ?_ ?_ ?_ ?_ h
    · rintro x hx
      exact ⟨x, Submodule.subset_span hx, 1, by rw [mk'_one, map_one, one_smul]⟩
    · exact ⟨0, Submodule.zero_mem _, 1, by rw [mk'_one, map_one, one_smul]⟩
    · rintro _ _ _ _ ⟨y, hy, z, rfl⟩ ⟨y', hy', z', rfl⟩
      refine
        ⟨(z' : R) • y + (z : R) • y',
          Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hy'), z * z', ?_⟩
      rw [smul_add, ← IsScalarTower.algebraMap_smul S (z : R), ←
        IsScalarTower.algebraMap_smul S (z' : R), smul_smul, smul_smul]
      congr 1
      · rw [← mul_one (1 : R), mk'_mul, mul_assoc, mk'_spec, map_one, mul_one, mul_one]
      · rw [← mul_one (1 : R), mk'_mul, mul_right_comm, mk'_spec, map_one, mul_one, one_mul]
    · rintro a _ _ ⟨y, hy, z, rfl⟩
      obtain ⟨y', z', rfl⟩ := exists_mk'_eq M a
      refine ⟨y' • y, Submodule.smul_mem _ _ hy, z' * z, ?_⟩
      rw [← IsScalarTower.algebraMap_smul S y', smul_smul, ← mk'_mul, smul_smul,
        mul_comm (mk' S _ _), mul_mk'_eq_mk'_of_mul]
  · rintro ⟨y, hy, z, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.span_subset_span R S _ hy)
/-
**IsLocalization.mem_span_map** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：mem_span_map {x : S} {a : Set R} : x in Ideal.span (algebraMap R S '' a) ↔
 exists y in Ideal.span a, exists z : M, x = mk' S y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.mem_span_iff`：mem_span_iff {N : Type*} [AddCommMonoid N] 
[Module R N] [Module S N] [IsScalarTower R S N] {x : N} {a : Set N} : x in Submo
dule.span S a ↔ e…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.coeSubmodule_span`：coeSubmodule_span (s : Set R) : coeSub
module S (Ideal.span s) = Submodule.span R (algebraMap R S '' s)
· 使用定理 `Algebra.linearMap_apply`：linearMap_apply (r : R) : Algebra.linearMap R A
 r = algebraMap R A r
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsLocalization.mul_mk'_eq_mk'_of_mul`：∀ {R : Type u_1} [inst : CommSemir
ing R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Al
gebra R S] [inst_3 : IsLoc…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Submodule.map_mem_span_algebraMap_image`：map_mem_span_algebraMap_image {
S T : Type*} [CommSemiring S] [Semiring T] [Algebra R S] [Algebra R T] [Algebra 
S T] [IsScalarTower R S T] (x…
-/
theorem mem_span_map {x : S} {a : Set R} :
    x ∈ Ideal.span (algebraMap R S '' a) ↔ ∃ y ∈ Ideal.span a, ∃ z : M, x = mk' S y z := by
  refine (mem_span_iff M).trans ?_
  constructor
  · rw [← coeSubmodule_span]
    rintro ⟨_, ⟨y, hy, rfl⟩, z, hz⟩
    refine ⟨y, hy, z, ?_⟩
    rw [hz, Algebra.linearMap_apply, smul_eq_mul, mul_comm, mul_mk'_eq_mk'_of_mul, mul_one]
  · rintro ⟨y, hy, z, hz⟩
    refine ⟨algebraMap R S y, Submodule.map_mem_span_algebraMap_image _ _ hy, z, ?_⟩
    rw [hz, smul_eq_mul, mul_comm, mul_mk'_eq_mk'_of_mul, mul_one]

end IsLocalization

namespace IsFractionRing

open IsLocalization

variable {R K : Type*}

section CommRing

variable [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]

@[simp, mono, gcongr]
/-
**IsFractionRing.coeSubmodule_le_coeSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `IsFract
ionRing`。
形式化陈述：coeSubmodule_le_coeSubmodule {I J : Ideal R} : coeSubmodule K I <= coeSubm
odule K J ↔ I <= J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.coeSubmodule_le_coeSubmodule`：coeSubmodule_le_coeSubmodul
e (h : M <= nonZeroDivisors R) {I J : Ideal R} : coeSubmodule S I <= coeSubmodul
e S J ↔ I <= J
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem coeSubmodule_le_coeSubmodule {I J : Ideal R} :
    coeSubmodule K I ≤ coeSubmodule K J ↔ I ≤ J :=
  IsLocalization.coeSubmodule_le_coeSubmodule le_rfl

@[gcongr, mono]
/-
**IsFractionRing.coeSubmodule_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRi
ng`。
形式化陈述：coeSubmodule_strictMono : StrictMono (coeSubmodule K : Ideal R -> Submodul
e R K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_of_le_iff_le`：strictMono_of_le_iff_le [Preorder α] [Preorder 
β] {f : α -> β} (h : forall x y, x <= y ↔ f x <= f y) : StrictMono f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `IsFractionRing.coeSubmodule_le_coeSubmodule`：coeSubmodule_le_coeSubmodul
e {I J : Ideal R} : coeSubmodule K I <= coeSubmodule K J ↔ I <= J
-/
theorem coeSubmodule_strictMono : StrictMono (coeSubmodule K : Ideal R → Submodule R K) :=
  strictMono_of_le_iff_le fun _ _ => coeSubmodule_le_coeSubmodule.symm

variable (R K)
/-
**IsFractionRing.coeSubmodule_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRin
g`。
形式化陈述：coeSubmodule_injective : Function.Injective (coeSubmodule K : Ideal R -> S
ubmodule R K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_eq_imp_le`：Function.Injective.of_eq_imp_le [Partia
lOrder α] {f : α -> β} (h : forall {x y}, f x = f y -> x <= y) : f.Injective
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsFractionRing.coeSubmodule_le_coeSubmodule`：coeSubmodule_le_coeSubmodul
e {I J : Ideal R} : coeSubmodule K I <= coeSubmodule K J ↔ I <= J
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem coeSubmodule_injective : Function.Injective (coeSubmodule K : Ideal R → Submodule R K) :=
  .of_eq_imp_le fun hl => coeSubmodule_le_coeSubmodule.mp hl.le

@[simp]
/-
**IsFractionRing.coeSubmodule_isPrincipal** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionR
ing`。
形式化陈述：coeSubmodule_isPrincipal {I : Ideal R} : (coeSubmodule K I).IsPrincipal ↔ 
I.IsPrincipal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.coeSubmodule_isPrincipal`：coeSubmodule_isPrincipal {I : I
deal R} (h : M <= nonZeroDivisors R) : (coeSubmodule S I).IsPrincipal ↔ I.IsPrin
cipal
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem coeSubmodule_isPrincipal {I : Ideal R} : (coeSubmodule K I).IsPrincipal ↔ I.IsPrincipal :=
  IsLocalization.coeSubmodule_isPrincipal _ le_rfl

end CommRing

end IsFractionRing

