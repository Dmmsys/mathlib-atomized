/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Away.Lemmas

/-!
# Target local closure of ring homomorphism properties

If `P` is a property of ring homomorphisms, we call `Locally P` the closure of `P` with
respect to standard open coverings on the (algebraic) target (i.e. geometric source). Hence
for `f : R →+* S`, the property `Locally P` holds if it holds locally on `S`, i.e. if there exists
a subset `{ t }` of `S` generating the unit ideal, such that `P` holds for all compositions
`R →+* Sₜ`.

Assuming without further mention that `P` is stable under composition with isomorphisms,
`Locally P` is local on the target by construction, i.e. it satisfies
`RingHom.OfLocalizationSpanTarget`. If `P` itself is local on the target,
`Locally P` coincides with `P`.

The `Locally` construction preserves various properties of `P`, e.g. if `P` is stable under
composition, base change, etc., so is `Locally P`.

## Main results

- `RingHom.locally_ofLocalizationSpanTarget`: `Locally P` is local on the target.
- `RingHom.locally_holdsForLocalizationAway`: `Locally P` holds for localization away maps
  if `P` does.
- `RingHom.locally_isStableUnderBaseChange`: `Locally P` is stable under base change if `P` is.
- `RingHom.locally_stableUnderComposition`: `Locally P` is stable under composition
  if `P` is and `P` is preserved under localizations.
- `RingHom.locally_stableUnderCompositionWithLocalizationAwayTarget` and
  `RingHom.locally_stableUnderCompositionWithLocalizationAwaySource`: `Locally P` is stable under
  composition with localization away maps if `P` is.
- `RingHom.locally_localizationPreserves`: If `P` is preserved by localizations, then so is
  `Locally P`.

-/

@[expose] public section

universe u v

open TensorProduct

namespace RingHom

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop)

/--
For a property of ring homomorphisms `P`, `Locally P` holds for `f : R →+* S` if
it holds locally on `S`, i.e. if there exists a subset `{ t }` of `S` generating
the unit ideal, such that `P` holds for all compositions `R →+* Sₜ`.

We may require `s` to be finite here, for the equivalence, see `locally_iff_finite`.
-/
/-
**RingHom.Locally** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：Locally {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) : Prop
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a property of ring homomorphisms `P`, `Locally P` holds for `f : R →+* S` if
it holds locally on `S`, i.e. if there exists a subset `{ t }` of `S` generating
the unit ideal, such that `P` holds for all compositions `R →+* Sₜ`.

We may require `s` to be finite here, for the equivalence, see `locally_iff_fini
te`.
-/
def Locally {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  ∃ (s : Set S) (_ : Ideal.span s = ⊤),
    ∀ t ∈ s, P ((algebraMap S (Localization.Away t)).comp f)

variable {R S : Type u} [CommRing R] [CommRing S]
/-
**RingHom.locally_iff_span_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_iff_span_eq_top {f : R ->+* S} : Locally P f ↔ Ideal.span {g : S |
 P ((algebraMap S (Localization.Away g)).comp f)} = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
-/
lemma locally_iff_span_eq_top {f : R →+* S} :
    Locally P f ↔ Ideal.span {g : S | P ((algebraMap S (Localization.Away g)).comp f)} = ⊤ := by
  refine ⟨fun ⟨s, hs, h⟩ ↦ ?_, fun h ↦ ⟨_, h, fun g hg ↦ hg⟩⟩
  rw [eq_top_iff, ← hs, Ideal.span_le]
  intro g hg
  exact Ideal.subset_span (h _ hg)

alias ⟨Locally.span_eq_top, _⟩ := locally_iff_span_eq_top
/-
**RingHom.locally_iff_finite** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_iff_finite (f : R ->+* S) : Locally P f ↔ exists (s : Finset S) (_
 : Ideal.span (s : Set S) = ⊤), forall t in s, P ((algebraMap S (Localization.Aw
ay t)).comp f)
参数：f : R ->+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_eq_top_iff_finite`：span_eq_top_iff_finite (s : Set α) : span 
s = ⊤ ↔ exists s' : Finset α, ↑s' subseteq s ∧ span (s' : Set α) = ⊤
-/
lemma locally_iff_finite (f : R →+* S) :
    Locally P f ↔ ∃ (s : Finset S) (_ : Ideal.span (s : Set S) = ⊤),
      ∀ t ∈ s, P ((algebraMap S (Localization.Away t)).comp f) := by
  constructor
  · intro ⟨s, hsone, hs⟩
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hsone
    exact ⟨s', h₂, fun t ht ↦ hs t (h₁ ht)⟩
  · intro ⟨s, hsone, hs⟩
    use s, hsone, hs

variable {P}

/-- If `P` respects isomorphisms, to check `P` holds locally for `f : R →+* S`, it suffices
to check `P` holds on a standard open cover. -/
/-
**RingHom.locally_of_exists** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_of_exists (hP : RespectsIso P) (f : R ->+* S) {ι : Type*} (s : ι -
> S) (hsone : Ideal.span (Set.range s) = ⊤) (Sₜ : ι -> Type u) [forall i, CommRi
ng (Sₜ i)] [forall i, Algebra S (Sₜ i)] [forall i, IsLocalization.Away (s i) (Sₜ
 i)] (hf : forall i, P ((algebraMap S (Sₜ i)).comp f)) : Locally P f
参数：hP : RespectsIso P；f : R ->+* S；s : ι -> S；hsone : Ideal.span (Set.range s) =
 ⊤；Sₜ : ι -> Type u；Sₜ i；Sₜ i；s i；Sₜ i；hf : forall i, P ((algebraMap S (Sₜ i)).c
omp f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If `P` respects isomorphisms, to check `P` holds locally for `f : R →+* S`, it s
uffices
to check `P` holds on a standard open cover.
-/
lemma locally_of_exists (hP : RespectsIso P) (f : R →+* S) {ι : Type*} (s : ι → S)
    (hsone : Ideal.span (Set.range s) = ⊤)
    (Sₜ : ι → Type u) [∀ i, CommRing (Sₜ i)] [∀ i, Algebra S (Sₜ i)]
    [∀ i, IsLocalization.Away (s i) (Sₜ i)] (hf : ∀ i, P ((algebraMap S (Sₜ i)).comp f)) :
    Locally P f := by
  use Set.range s, hsone
  rintro - ⟨i, rfl⟩
  let e : Localization.Away (s i) ≃+* Sₜ i :=
    (IsLocalization.algEquiv (Submonoid.powers (s i)) _ _).toRingEquiv
  have : algebraMap S (Localization.Away (s i)) = e.symm.toRingHom.comp (algebraMap S (Sₜ i)) :=
    RingHom.ext (fun x ↦ (AlgEquiv.commutes (IsLocalization.algEquiv _ _ _).symm _).symm)
  rw [this, RingHom.comp_assoc]
  exact hP.left _ _ (hf i)

/-- Equivalence variant of `locally_of_exists`. This is sometimes easier to use, if the
`IsLocalization.Away` instance can't be automatically inferred. -/
/-
**RingHom.locally_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_iff_exists (hP : RespectsIso P) (f : R ->+* S) : Locally P f ↔ exi
sts (ι : Type u) (s : ι -> S) (_ : Ideal.span (Set.range s) = ⊤) (Sₜ : ι -> Type
 u) (_ : (i : ι) -> CommRing (Sₜ i)) (_ : (i : ι) -> Algebra S (Sₜ i)) (_ : (i :
 ι) -> IsLocalization.Away (s i : S) (Sₜ i)), forall i, P ((algebraMap S (Sₜ i))
.comp f)
参数：hP : RespectsIso P；f : R ->+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `RingHom.locally_of_exists`：locally_of_exists (hP : RespectsIso P) (f : R
 ->+* S) {ι : Type*} (s : ι -> S) (hsone : Ideal.span (Set.range s) = ⊤) (Sₜ : ι
 -> Type u) [fo…

--- 原说明 ---
Equivalence variant of `locally_of_exists`. This is sometimes easier to use, if 
the
`IsLocalization.Away` instance can't be automatically inferred.
-/
lemma locally_iff_exists (hP : RespectsIso P) (f : R →+* S) :
    Locally P f ↔ ∃ (ι : Type u) (s : ι → S) (_ : Ideal.span (Set.range s) = ⊤) (Sₜ : ι → Type u)
      (_ : (i : ι) → CommRing (Sₜ i)) (_ : (i : ι) → Algebra S (Sₜ i))
      (_ : (i : ι) → IsLocalization.Away (s i : S) (Sₜ i)),
      ∀ i, P ((algebraMap S (Sₜ i)).comp f) :=
  ⟨fun ⟨s, hsone, hs⟩ ↦ ⟨s, fun t : s ↦ (t : S), by simpa, fun t ↦ Localization.Away (t : S),
      inferInstance, inferInstance, inferInstance, fun t ↦ hs t.val t.property⟩,
    fun ⟨ι, s, hsone, Sₜ, _, _, hislocal, hs⟩ ↦ locally_of_exists hP f s hsone Sₜ hs⟩

/-- In the definition of `Locally` we may replace `Localization.Away` with an arbitrary
algebra satisfying `IsLocalization.Away`. -/
/-
**RingHom.locally_iff_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_iff_isLocalization (hP : RespectsIso P) (f : R ->+* S) : Locally P
 f ↔ exists (s : Finset S) (_ : Ideal.span (s : Set S) = ⊤), forall t in s, fora
ll (Sₜ : Type u) [CommRing Sₜ] [Algebra S Sₜ] [IsLocalization.Away t Sₜ], P ((al
gebraMap S Sₜ).comp f)
参数：hP : RespectsIso P；f : R ->+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.locally_iff_finite`：locally_iff_finite (f : R ->+* S) : Locally 
P f ↔ exists (s : Finset S) (_ : Ideal.span (s : Set S) = ⊤), forall t in s, P (
(algebraMap S (L…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
In the definition of `Locally` we may replace `Localization.Away` with an arbitr
ary
algebra satisfying `IsLocalization.Away`.
-/
lemma locally_iff_isLocalization (hP : RespectsIso P) (f : R →+* S) :
    Locally P f ↔ ∃ (s : Finset S) (_ : Ideal.span (s : Set S) = ⊤),
      ∀ t ∈ s, ∀ (Sₜ : Type u) [CommRing Sₜ] [Algebra S Sₜ] [IsLocalization.Away t Sₜ],
      P ((algebraMap S Sₜ).comp f) := by
  rw [locally_iff_finite P f]
  refine ⟨fun ⟨s, hsone, hs⟩ ↦ ⟨s, hsone, fun t ht Sₜ _ _ _ ↦ ?_⟩, fun ⟨s, hsone, hs⟩ ↦ ?_⟩
  · let e : Localization.Away t ≃+* Sₜ :=
      (IsLocalization.algEquiv (Submonoid.powers t) _ _).toRingEquiv
    have : algebraMap S Sₜ = e.toRingHom.comp (algebraMap S (Localization.Away t)) :=
      RingHom.ext (fun x ↦ (AlgEquiv.commutes (IsLocalization.algEquiv _ _ _) _).symm)
    rw [this, RingHom.comp_assoc]
    exact hP.left _ _ (hs t ht)
  · exact ⟨s, hsone, fun t ht ↦ hs t ht _⟩

/-- If `f` satisfies `P`, then in particular it satisfies `Locally P`. -/
/-
**RingHom.locally_of** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_of (hP : RespectsIso P) (f : R ->+* S) (hf : P f) : Locally P f
参数：hP : RespectsIso P；f : R ->+* S；hf : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submonoid.powers_one`：powers_one : powers (1 : M) = ⊥
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.span_singleton_one`：span_singleton_one : span ({1} : Set α) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If `f` satisfies `P`, then in particular it satisfies `Locally P`.
-/
lemma locally_of (hP : RespectsIso P) (f : R →+* S) (hf : P f) : Locally P f := by
  use {1}
  let e : S ≃+* Localization.Away (1 : S) :=
    (IsLocalization.atUnits S (Submonoid.powers 1) (by simp)).toRingEquiv
  simp only [Set.mem_singleton_iff, forall_eq, Ideal.span_singleton_one, exists_const]
  exact hP.left f e hf
/-
**RingHom.locally_of_locally** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_of_locally {Q : forall {R S : Type u} [CommRing R] [CommRing S], (
R ->+* S) -> Prop} (hPQ : forall {R S : Type u} [CommRing R] [CommRing S] {f : R
 ->+* S}, P f -> Q f) {R S : Type u} [CommRing R] [CommRing S] {f : R ->+* S} (h
f : Locally P f) : Locally Q f
参数：R ->+* S；hPQ : forall {R S : Type u} [CommRing R] [CommRing S] {f : R ->+* S}
, P f -> Q f；hf : Locally P f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma locally_of_locally {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hPQ : ∀ {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}, P f → Q f)
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S} (hf : Locally P f) : Locally Q f := by
  obtain ⟨s, hsone, hs⟩ := hf
  exact ⟨s, hsone, fun t ht ↦ hPQ (hs t ht)⟩

/-- If `P` is local on the target, then `Locally P` coincides with `P`. -/
/-
**RingHom.locally_iff_of_localizationSpanTarget** 是 Mathlib 中的一个引理，位于命名空间 `RingH
om`。
形式化陈述：locally_iff_of_localizationSpanTarget (hPi : RespectsIso P) (hPs : OfLocal
izationSpanTarget P) {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) : L
ocally P f ↔ P f
参数：hPi : RespectsIso P；hPs : OfLocalizationSpanTarget P；f : R ->+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `RingHom.locally_of`：locally_of (hP : RespectsIso P) (f : R ->+* S) (hf :
 P f) : Locally P f

--- 原说明 ---
If `P` is local on the target, then `Locally P` coincides with `P`.
-/
lemma locally_iff_of_localizationSpanTarget (hPi : RespectsIso P)
    (hPs : OfLocalizationSpanTarget P) {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Locally P f ↔ P f :=
  ⟨fun ⟨s, hsone, hs⟩ ↦ hPs f s hsone (fun a ↦ hs a.val a.property), locally_of hPi f⟩

section OfLocalizationSpanTarget

/-- `Locally P` is local on the target. -/
/-
**RingHom.locally_ofLocalizationSpanTarget** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_ofLocalizationSpanTarget (hP : RespectsIso P) : OfLocalizationSpan
Target (Locally P)
参数：hP : RespectsIso P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.locally_iff_exists`：locally_iff_exists (hP : RespectsIso P) (f :
 R ->+* S) : Locally P f ↔ exists (ι : Type u) (s : ι -> S) (_ : Ideal.span (Set
.range s) = ⊤) (…
· 使用引理 `IsLocalization.Away.span_range_mulNumerator_eq_top`：span_range_mulNumera
tor_eq_top {s : Set R} (hsone : Ideal.span s = ⊤) {Rₜ : s -> Type*} [forall t, C
ommRing (Rₜ t)] [forall t, Algebra R (Rₜ…
· 使用引理 `IsLocalization.Away.of_associated`：of_associated {r r' : R} (h : Associa
ted r r') [IsLocalization.Away r S] : IsLocalization.Away r' S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsLocalization.Away.sec_spec`：sec_spec (s : S) : s * (algebraMap R S) (x
 ^ (IsLocalization.Away.sec x s).2) = algebraMap R S (IsLocalization.Away.sec x 
s).1
· 使用定理 `associated_mul_unit_right`：associated_mul_unit_right {N : Type*} [Monoid
 N] (a u : N) (hu : IsUnit u) : Associated a (a * u)
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用引理 `IsLocalization.Away.algebraMap_isUnit`：algebraMap_isUnit : IsUnit (algeb
raMap R S x)
· 使用引理 `IsLocalization.Away.mul'`：mul' (T : Type*) [CommSemiring T] [Algebra S T
] [Algebra R T] [IsScalarTower R S T] (x y : R) [IsLocalization.Away x S] [IsLoc
alization.Away…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
`Locally P` is local on the target.
-/
lemma locally_ofLocalizationSpanTarget (hP : RespectsIso P) :
    OfLocalizationSpanTarget (Locally P) := by
  intro R S _ _ f s hsone hs
  choose t htone ht using hs
  rw [locally_iff_exists hP]
  refine ⟨(a : s) × t a, IsLocalization.Away.mulNumerator s t,
      IsLocalization.Away.span_range_mulNumerator_eq_top hsone htone,
      fun ⟨a, b⟩ ↦ Localization.Away b.val, inferInstance, inferInstance, fun ⟨a, b⟩ ↦ ?_, ?_⟩
  · have : IsLocalization.Away ((algebraMap S (Localization.Away a.val))
        (IsLocalization.Away.sec a.val b.val).1) (Localization.Away b.val) := by
      apply IsLocalization.Away.of_associated (r := b.val)
      rw [← IsLocalization.Away.sec_spec]
      apply associated_mul_unit_right
      rw [map_pow _ _]
      exact IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit _)
    apply IsLocalization.Away.mul' (Localization.Away a.val) (Localization.Away b.val)
  · intro ⟨a, b⟩
    rw [IsScalarTower.algebraMap_eq S (Localization.Away a.val) (Localization.Away b.val)]
    apply ht _ _ b.property

end OfLocalizationSpanTarget

section Stability

set_option backward.isDefEq.respectTransparency.types false in
/-- If `P` respects isomorphism, so does `Locally P`. -/
/-
**RingHom.locally_respectsIso** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_respectsIso (hPi : RespectsIso P) : RespectsIso (Locally P) where 
left {R S T} _ _ _ f e
参数：hPi : RespectsIso P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用定理 `Submonoid.map_powers`：map_powers {N : Type*} {F : Type*} [Monoid N] [Fun
Like F M N] [MonoidHomClass F M N] (f : F) (m : M) : (powers m).map f = powers (
f m)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalization.ringEquivOfRingEquiv_apply`：∀ {R : Type u_1} [inst : Comm
Semiring R] {M : Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2
 : Algebra R S] {P : Type u_3} …
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `P` respects isomorphism, so does `Locally P`.
-/
lemma locally_respectsIso (hPi : RespectsIso P) : RespectsIso (Locally P) where
  left {R S T} _ _ _ f e := fun ⟨s, hsone, hs⟩ ↦ by
    refine ⟨e '' s, ?_, ?_⟩
    · rw [← Ideal.map_span, hsone, Ideal.map_top]
    · rintro - ⟨a, ha, rfl⟩
      let e' : Localization.Away a ≃+* Localization.Away (e a) :=
        IsLocalization.ringEquivOfRingEquiv _ _ e (Submonoid.map_powers e a)
      have : (algebraMap T (Localization.Away (e a))).comp e.toRingHom =
          e'.toRingHom.comp (algebraMap S (Localization.Away a)) := by
        ext x
        simp [e']
      rw [← RingHom.comp_assoc, this, RingHom.comp_assoc]
      apply hPi.left
      exact hs a ha
  right {R S T} _ _ _ f e := fun ⟨s, hsone, hs⟩ ↦
    ⟨s, hsone, fun a ha ↦ (RingHom.comp_assoc _ _ _).symm ▸ hPi.right _ _ (hs a ha)⟩

/-- If `P` holds for localization away maps, then so does `Locally P`. -/
/-
**RingHom.locally_holdsForLocalizationAway** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_holdsForLocalizationAway (hPa : HoldsForLocalizationAway P) : Hold
sForLocalizationAway (Locally P)
参数：hPa : HoldsForLocalizationAway P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_singleton_one`：span_singleton_one : span ({1} : Set α) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Submonoid.powers_one`：powers_one : powers (1 : M) = ⊥
· 使用定理 `IsLocalization.isLocalization_of_algEquiv`：isLocalization_of_algEquiv [A
lgebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) : IsLocalization M P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)

--- 原说明 ---
If `P` holds for localization away maps, then so does `Locally P`.
-/
lemma locally_holdsForLocalizationAway (hPa : HoldsForLocalizationAway P) :
    HoldsForLocalizationAway (Locally P) := by
  introv R _
  use {1}
  simp only [Set.mem_singleton_iff, forall_eq, Ideal.span_singleton_one, exists_const]
  let e : S ≃ₐ[R] (Localization.Away (1 : S)) :=
    (IsLocalization.atUnits S (Submonoid.powers 1) (by simp)).restrictScalars R
  have : IsLocalization.Away r (Localization.Away (1 : S)) :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r) e
  rw [← IsScalarTower.algebraMap_eq]
  apply hPa _ r

/-- If `P` preserves localizations, then `Locally P` is stable under composition if `P` is. -/
/-
**RingHom.locally_stableUnderComposition** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_stableUnderComposition (hPi : RespectsIso P) (hPl : LocalizationPr
eserves P) (hPc : StableUnderComposition P) : StableUnderComposition (Locally P)
参数：hPi : RespectsIso P；hPl : LocalizationPreserves P；hPc : StableUnderCompositio
n P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.locally_iff_finite`：locally_iff_finite (f : R ->+* S) : Locally 
P f ↔ exists (s : Finset S) (_ : Ideal.span (s : Set S) = ⊤), forall t in s, P (
(algebraMap S (L…
· 使用引理 `RingHom.locally_iff_exists`：locally_iff_exists (hP : RespectsIso P) (f :
 R ->+* S) : Locally P f ↔ exists (ι : Type u) (s : ι -> S) (_ : Ideal.span (Set
.range s) = ⊤) (…
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Fintype.sum_prod_type`：∀ {γ : Type u_3} {α₁ : Type u_4} {α₂ : Type u_5} 
[inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid γ]   (f : α₁ ×
 α₂ → γ), ∑…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `P` preserves localizations, then `Locally P` is stable under composition if 
`P` is.
-/
lemma locally_stableUnderComposition (hPi : RespectsIso P) (hPl : LocalizationPreserves P)
    (hPc : StableUnderComposition P) :
    StableUnderComposition (Locally P) := by
  classical
  intro R S T _ _ _ f g hf hg
  rw [locally_iff_finite] at hf hg
  obtain ⟨sf, hsfone, hsf⟩ := hf
  obtain ⟨sg, hsgone, hsg⟩ := hg
  rw [locally_iff_exists hPi]
  refine ⟨sf × sg, fun (a, b) ↦ g a * b, ?_,
      fun (a, b) ↦ Localization.Away ((algebraMap T (Localization.Away b.val)) (g a.val)),
      inferInstance, inferInstance, inferInstance, ?_⟩
  · rw [eq_top_iff, ← hsgone, Ideal.span_le]
    intro t ht
    have : 1 ∈ Ideal.span (Set.range <| fun a : sf ↦ a.val) := by simp [hsfone]
    simp only [Ideal.mem_span_range_iff_exists_fun, SetLike.mem_coe] at this ⊢
    obtain ⟨cf, hcf⟩ := this
    let cg : sg → T := Pi.single ⟨t, ht⟩ 1
    use fun (a, b) ↦ g (cf a) * cg b
    simp [cg, Pi.single_apply, Fintype.sum_prod_type, ← mul_assoc, ← Finset.sum_mul, ← map_mul,
      ← map_sum, hcf] at hcf ⊢
  · intro ⟨a, b⟩
    let g' := (algebraMap T (Localization.Away b.val)).comp g
    let a' := (algebraMap T (Localization.Away b.val)) (g a.val)
    have : (algebraMap T <| Localization.Away a').comp (g.comp f) =
        (Localization.awayMap g' a.val).comp ((algebraMap S (Localization.Away a.val)).comp f) := by
      ext x
      simp only [coe_comp, Function.comp_apply, a']
      change _ = Localization.awayMap g' a.val (algebraMap S _ (f x))
      simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
      rfl
    simp only [this, a']
    apply hPc _ _ (hsf a.val a.property)
    apply @hPl _ _ _ _ g' _ _ _ _ _ _ _ _ ?_ (hsg b.val b.property)
    exact IsLocalization.Away.instMapRingHomPowersOfCoe (Localization.Away (g' a.val)) a.val

/-- If `P` is stable under composition with localization away maps on the right,
then so is `Locally P`. -/
/-
**RingHom.locally_stableUnderCompositionWithLocalizationAwayTarget** 是 Mathlib 中
的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_stableUnderCompositionWithLocalizationAwayTarget (hPa : StableUnde
rCompositionWithLocalizationAwayTarget P) : StableUnderCompositionWithLocalizati
onAwayTarget (Locally P)
参数：hPa : StableUnderCompositionWithLocalizationAwayTarget P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用引理 `IsLocalization.Away.commutes`：commutes {R : Type*} [CommSemiring R] (S₁ 
S₂ T : Type*) [CommSemiring S₁] [CommSemiring S₂] [CommSemiring T] [Algebra R S₁
] [Algebra R S₂] […

--- 原说明 ---
If `P` is stable under composition with localization away maps on the right,
then so is `Locally P`.
-/
lemma locally_stableUnderCompositionWithLocalizationAwayTarget
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) :
    StableUnderCompositionWithLocalizationAwayTarget (Locally P) := by
  intro R S T _ _ _ _ t _ f hf
  obtain ⟨s, hsone, hs⟩ := hf
  refine ⟨algebraMap S T '' s, ?_, ?_⟩
  · rw [← Ideal.map_span, hsone, Ideal.map_top]
  · rintro - ⟨a, ha, rfl⟩
    let : Algebra (Localization.Away a) (Localization.Away (algebraMap S T a)) :=
      (IsLocalization.Away.map _ _ (algebraMap S T) a).toAlgebra
    have : (algebraMap (Localization.Away a) (Localization.Away (algebraMap S T a))).comp
        (algebraMap S (Localization.Away a)) =
        (algebraMap T (Localization.Away (algebraMap S T a))).comp (algebraMap S T) := by
      simp [algebraMap_toAlgebra, IsLocalization.Away.map]
    rw [← comp_assoc, ← this, comp_assoc]
    have : IsScalarTower S (Localization.Away a) (Localization.Away ((algebraMap S T) a)) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      simp [algebraMap_toAlgebra, IsLocalization.Away.map, ← IsScalarTower.algebraMap_apply]
    have : IsLocalization.Away (algebraMap S (Localization.Away a) t)
        (Localization.Away (algebraMap S T a)) :=
      IsLocalization.Away.commutes _ T ((Localization.Away (algebraMap S T a))) a t
    apply hPa _ (algebraMap S (Localization.Away a) t)
    apply hs a ha

@[deprecated (since := "2026-02-11")]
alias locally_StableUnderCompositionWithLocalizationAwayTarget :=
  locally_stableUnderCompositionWithLocalizationAwayTarget

/-- If `P` is stable under composition with localization away maps on the left,
then so is `Locally P`. -/
/-
**RingHom.locally_stableUnderCompositionWithLocalizationAwaySource** 是 Mathlib 中
的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_stableUnderCompositionWithLocalizationAwaySource (hPa : StableUnde
rCompositionWithLocalizationAwaySource P) : StableUnderCompositionWithLocalizati
onAwaySource (Locally P)
参数：hPa : StableUnderCompositionWithLocalizationAwaySource P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)

--- 原说明 ---
If `P` is stable under composition with localization away maps on the left,
then so is `Locally P`.
-/
lemma locally_stableUnderCompositionWithLocalizationAwaySource
    (hPa : StableUnderCompositionWithLocalizationAwaySource P) :
    StableUnderCompositionWithLocalizationAwaySource (Locally P) := by
  intro R S T _ _ _ _ r _ f ⟨s, hsone, hs⟩
  refine ⟨s, hsone, fun t ht ↦ ?_⟩
  rw [← comp_assoc]
  exact hPa _ r _ (hs t ht)

@[deprecated (since := "2026-02-11")]
alias locally_StableUnderCompositionWithLocalizationAwaySource :=
  locally_stableUnderCompositionWithLocalizationAwaySource

/-- If `P` is stable under base change, then so is `Locally P`. -/
/-
**RingHom.locally_isStableUnderBaseChange** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_isStableUnderBaseChange (hPi : RespectsIso P) (hPb : IsStableUnder
BaseChange P) : IsStableUnderBaseChange (Locally P)
参数：hPi : RespectsIso P；hPb : IsStableUnderBaseChange P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用引理 `RingHom.locally_respectsIso`：locally_respectsIso (hPi : RespectsIso P) :
 RespectsIso (Locally P) where left {R S T} _ _ _ f e
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.locally_iff_span_eq_top`：locally_iff_span_eq_top {f : R ->+* S} 
: Locally P f ↔ Ideal.span {g : S | P ((algebraMap S (Localization.Away g)).comp
 f)} = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.Locally.span_eq_top`：∀ (P : {R S : Type u} → [inst : CommRing R]
 → [inst_1 : CommRing S] → (R →+* S) → Prop) {R S : Type u}   [inst : CommRing R
] [inst_1 : CommR…
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `RingHom.IsStableUnderBaseChange.tensorProduct`：∀ {P : {R S : Type u} → [
inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   (RingHom.IsSta
bleUnderBaseChange fun {R S} [CommR…

--- 原说明 ---
If `P` is stable under base change, then so is `Locally P`.
-/
lemma locally_isStableUnderBaseChange (hPi : RespectsIso P) (hPb : IsStableUnderBaseChange P) :
    IsStableUnderBaseChange (Locally P) := by
  apply IsStableUnderBaseChange.mk (locally_respectsIso hPi)
  introv hf
  rw [locally_iff_span_eq_top, eq_top_iff, ← Ideal.map_top Algebra.TensorProduct.includeRight,
    ← hf.span_eq_top, Ideal.map_le_iff_le_comap, Ideal.span_le]
  intro g hg
  apply Ideal.subset_span
  simp only [Set.mem_ofPred_eq, Algebra.TensorProduct.includeRight_apply,
    ← IsScalarTower.algebraMap_eq] at hg ⊢
  let e := IsLocalization.Away.tensorProductEquivTMulRight R S g (Localization.Away g)
  rw [← e.toAlgHom.comp_algebraMap]
  exact hPi.left _ _ (hPb.tensorProduct _ hg)

/-- If `P` is preserved by localization away, then so is `Locally P`. -/
/-
**RingHom.locally_localizationAwayPreserves** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_localizationAwayPreserves (hPl : LocalizationAwayPreserves P) : Lo
calizationAwayPreserves (Locally P)
参数：hPl : LocalizationAwayPreserves P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.locally_iff_exists`：locally_iff_exists (hP : RespectsIso P) (f :
 R ->+* S) : Locally P f ↔ exists (ι : Type u) (s : ι -> S) (_ : Ideal.span (Set
.range s) = ⊤) (…
· 使用引理 `RingHom.LocalizationAwayPreserves.respectsIso`：RingHom.LocalizationAwayP
reserves.respectsIso (hP : LocalizationAwayPreserves P) : RespectsIso P where le
ft {R S T} _ _ _ f e hf
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submonoid.map.congr_simp`：∀ {M : Type u_1} {N : Type u_2} [inst : MulOne
Class M] [inst_1 : MulOneClass N] {F : Type u_4} [inst_2 : FunLike F M N]   [mc 
: MonoidHomCla…
· 使用定理 `Submonoid.map_powers`：map_powers {N : Type*} {F : Type*} [Monoid N] [Fun
Like F M N] [MonoidHomClass F M N] (f : F) (m : M) : (powers m).map f = powers (
f m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用引理 `IsLocalization.commutes`：commutes (S₁ S₂ T : Type*) [CommSemiring S₁] [C
ommSemiring S₂] [CommSemiring T] [Algebra R S₁] [Algebra R S₂] [Algebra R T] [Al
gebra S₁ T] […
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsLocalization.Away.instMapRingHomPowersOfCoe`：∀ {A : Type u_5} [inst : 
CommSemiring A] {B : Type u_6} [inst_1 : CommSemiring B] (Bₚ : Type u_8)   [inst
_2 : CommSemiring Bₚ] [inst_3 : Alg…
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `IsLocalization.Away.map.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (
S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] {P : Type u_3}   
[inst_3 : CommSemi…
· 使用定理 `IsLocalization.map_comp_map`：map_comp_map {A : Type*} [CommSemiring A] {
U : Submonoid A} {W} [CommSemiring W] [Algebra A W] [IsLocalization U W] {l : P 
->+* A} (hl : T <…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If `P` is preserved by localization away, then so is `Locally P`.
-/
lemma locally_localizationAwayPreserves (hPl : LocalizationAwayPreserves P) :
    LocalizationAwayPreserves (Locally P) := by
  introv R hf
  obtain ⟨s, hsone, hs⟩ := hf
  rw [locally_iff_exists hPl.respectsIso]
  let rₐ (a : s) : Localization.Away a.val := algebraMap _ _ (f r)
  let Sₐ (a : s) := Localization.Away (rₐ a)
  have (a : s) :
      IsLocalization.Away (((algebraMap S (Localization.Away a.val)).comp f) r) (Sₐ a) :=
    inferInstanceAs (IsLocalization.Away (rₐ a) (Sₐ a))
  have (a : s) : IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away a.val)
    (Submonoid.map f (Submonoid.powers r))) (Sₐ a) := by
    convert! (inferInstance : IsLocalization.Away (rₐ a) (Sₐ a))
    simp [rₐ, Algebra.algebraMapSubmonoid]
  have H (a : s) : Submonoid.powers (f r) ≤
      (Submonoid.powers (rₐ a)).comap (algebraMap S (Localization.Away a.val)) := by
    simp [rₐ, Submonoid.powers_le]
  let (a : s) : Algebra S' (Sₐ a) :=
    (IsLocalization.map (Sₐ a) (algebraMap S (Localization.Away a.val)) (H a)).toAlgebra
  have (a : s) : IsScalarTower S S' (Sₐ a) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.map_comp (H a)).symm
  refine ⟨s, fun a ↦ algebraMap S S' a.val, ?_, Sₐ,
      inferInstance, inferInstance, fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [← Set.image_eq_range, ← Ideal.map_span, hsone, Ideal.map_top]
  · convert!
    IsLocalization.commutes (T := Sₐ a) (M₁ := (Submonoid.powers r).map f) (S₁ := S') (S₂ :=
      Localization.Away a.val) (M₂ := Submonoid.powers a.val)
    simp [Algebra.algebraMapSubmonoid]
  · rw [algebraMap_toAlgebra, IsLocalization.Away.map, IsLocalization.map_comp_map]
    exact hPl ((algebraMap _ (Localization.Away a.val)).comp f) r R' (Sₐ a) (hs _ a.2)

/-- If `P` is preserved by localizations, then so is `Locally P`. -/
/-
**RingHom.locally_localizationPreserves** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_localizationPreserves (hPl : LocalizationPreserves P) : Localizati
onPreserves (Locally P)
参数：hPl : LocalizationPreserves P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.locally_iff_exists`：locally_iff_exists (hP : RespectsIso P) (f :
 R ->+* S) : Locally P f ↔ exists (ι : Type u) (s : ι -> S) (_ : Ideal.span (Set
.range s) = ⊤) (…
· 使用引理 `RingHom.LocalizationAwayPreserves.respectsIso`：RingHom.LocalizationAwayP
reserves.respectsIso (hP : LocalizationAwayPreserves P) : RespectsIso P where le
ft {R S T} _ _ _ f e hf
· 使用定理 `RingHom.LocalizationPreserves.away`：RingHom.LocalizationPreserves.away (
H : RingHom.LocalizationPreserves @P) : RingHom.LocalizationAwayPreserves P
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.map_map`：map_map (g : N ->* P) (f : M ->* N) : (S.map f).map g
 = S.map (g.comp f)
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submonoid.map_powers`：map_powers {N : Type*} {F : Type*} [Monoid N] [Fun
Like F M N] [MonoidHomClass F M N] (f : F) (m : M) : (powers m).map f = powers (
f m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsLocalization.commutes`：commutes (S₁ S₂ T : Type*) [CommSemiring S₁] [C
ommSemiring S₂] [CommSemiring T] [Algebra R S₁] [Algebra R S₂] [Algebra R T] [Al
gebra S₁ T] […
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `IsLocalization.map_comp_map`：map_comp_map {A : Type*} [CommSemiring A] {
U : Submonoid A} {W} [CommSemiring W] [Algebra A W] [IsLocalization U W] {l : P 
->+* A} (hl : T <…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If `P` is preserved by localizations, then so is `Locally P`.
-/
lemma locally_localizationPreserves (hPl : LocalizationPreserves P) :
    LocalizationPreserves (Locally P) := by
  introv R hf
  obtain ⟨s, hsone, hs⟩ := hf
  rw [locally_iff_exists hPl.away.respectsIso]
  let Mₐ (a : s) : Submonoid (Localization.Away a.val) :=
    (M.map f).map (algebraMap S (Localization.Away a.val))
  let Sₐ (a : s) := Localization (Mₐ a)
  have hM (a : s) : M.map ((algebraMap S (Localization.Away a.val)).comp f) = Mₐ a :=
    (M.map_map _ _).symm
  have (a : s) :
      IsLocalization (M.map ((algebraMap S (Localization.Away a.val)).comp f)) (Sₐ a) := by
    rw [hM]
    infer_instance
  have (a : s) :
      IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away a.val) (M.map f)) (Sₐ a) :=
    inferInstanceAs <| IsLocalization (Mₐ a) (Sₐ a)
  let (a : s) : Algebra S' (Sₐ a) :=
    (IsLocalization.map (Sₐ a) (algebraMap S (Localization.Away a.val))
      (M.map f).le_comap_map).toAlgebra
  have (a : s) : IsScalarTower S S' (Sₐ a) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.map_comp (M.map f).le_comap_map).symm
  refine ⟨s, fun a ↦ algebraMap S S' a.val, ?_, Sₐ,
      inferInstance, inferInstance, fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [← Set.image_eq_range, ← Ideal.map_span, hsone, Ideal.map_top]
  · convert!
    IsLocalization.commutes (T := Sₐ a) (M₁ := M.map f) (S₁ := S') (S₂ := Localization.Away a.val)
      (M₂ := Submonoid.powers a.val)
    simp [Algebra.algebraMapSubmonoid]
  · rw [algebraMap_toAlgebra, IsLocalization.map_comp_map]
    apply hPl
    exact hs a.val a.property

/-- If `P` is preserved by localizations and stable under composition with localization
away maps, then `Locally P` is a local property of ring homomorphisms. -/
/-
**RingHom.locally_propertyIsLocal** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：locally_propertyIsLocal (hPl : LocalizationAwayPreserves P) (hPa : StableU
nderCompositionWithLocalizationAway P) : PropertyIsLocal (Locally P) where local
izationAwayPreserves
参数：hPl : LocalizationAwayPreserves P；hPa : StableUnderCompositionWithLocalizatio
nAway P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.locally_localizationAwayPreserves`：locally_localizationAwayPrese
rves (hPl : LocalizationAwayPreserves P) : LocalizationAwayPreserves (Locally P)
· 使用引理 `RingHom.locally_ofLocalizationSpanTarget`：locally_ofLocalizationSpanTarg
et (hP : RespectsIso P) : OfLocalizationSpanTarget (Locally P)
· 使用引理 `RingHom.LocalizationAwayPreserves.respectsIso`：RingHom.LocalizationAwayP
reserves.respectsIso (hP : LocalizationAwayPreserves P) : RespectsIso P where le
ft {R S T} _ _ _ f e hf
· 使用定理 `RingHom.OfLocalizationSpanTarget.ofLocalizationSpan`：RingHom.OfLocalizat
ionSpanTarget.ofLocalizationSpan (hP : RingHom.OfLocalizationSpanTarget @P) (hP'
 : RingHom.StableUnderCompositionWithLoca…
· 使用引理 `RingHom.locally_stableUnderCompositionWithLocalizationAwaySource`：locall
y_stableUnderCompositionWithLocalizationAwaySource (hPa : StableUnderComposition
WithLocalizationAwaySource P) : StableUnderComposition…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `RingHom.locally_stableUnderCompositionWithLocalizationAwayTarget`：locall
y_stableUnderCompositionWithLocalizationAwayTarget (hPa : StableUnderComposition
WithLocalizationAwayTarget P) : StableUnderComposition…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `P` is preserved by localizations and stable under composition with localizat
ion
away maps, then `Locally P` is a local property of ring homomorphisms.
-/
lemma locally_propertyIsLocal (hPl : LocalizationAwayPreserves P)
    (hPa : StableUnderCompositionWithLocalizationAway P) : PropertyIsLocal (Locally P) where
  localizationAwayPreserves := locally_localizationAwayPreserves hPl
  StableUnderCompositionWithLocalizationAwayTarget :=
    locally_stableUnderCompositionWithLocalizationAwayTarget hPa.right
  ofLocalizationSpan := (locally_ofLocalizationSpanTarget hPl.respectsIso).ofLocalizationSpan
    (locally_stableUnderCompositionWithLocalizationAwaySource hPa.left)
  ofLocalizationSpanTarget := locally_ofLocalizationSpanTarget hPl.respectsIso

end Stability

end RingHom

