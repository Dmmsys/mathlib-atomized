/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.OpenImmersion

/-! # The meta properties of quasi-finite ring homomorphisms. -/

@[expose] public section

universe u

namespace RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- A ring hom `R →+* S` is quasi-finite if `S` is a quasi-finite `R`-algebra. -/
@[algebraize RingHom.QuasiFinite.toAlgebra]
/-
**RingHom.QuasiFinite** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：QuasiFinite {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) : Prop
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring hom `R →+* S` is quasi-finite if `S` is a quasi-finite `R`-algebra.
-/
def QuasiFinite {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  @Algebra.QuasiFinite R S _ _ f.toAlgebra

/-- Helper lemma for the `algebraize` tactic -/
/-
**RingHom.QuasiFinite.toAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.QuasiFinite`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
{f : R →+* S},   f.QuasiFinite → Algebra.QuasiFinite R S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper lemma for the `algebraize` tactic
-/
lemma QuasiFinite.toAlgebra {f : R →+* S} (hf : QuasiFinite f) :
    @Algebra.QuasiFinite R S _ _ f.toAlgebra := hf

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
/-
**RingHom.quasiFinite_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：quasiFinite_algebraMap [Algebra R S] : (algebraMap R S).QuasiFinite ↔ Alge
bra.QuasiFinite R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.QuasiFinite.eq_1`：∀ {R : Type u_4} {S : Type u_5} [inst : CommRi
ng R] [inst_1 : CommRing S] (f : R →+* S),   f.QuasiFinite = Algebra.QuasiFinite
 R S
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma quasiFinite_algebraMap [Algebra R S] :
    (algebraMap R S).QuasiFinite ↔ Algebra.QuasiFinite R S := by
  rw [RingHom.QuasiFinite, toAlgebra_algebraMap]
/-
**RingHom.QuasiFinite.comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.QuasiFinite`。
形式化陈述：∀ {T : Type u_3} [inst : CommRing T] {R : Type u_4} {S : Type u_5} [inst_1
 : CommRing R] [inst_2 : CommRing S]   {f : S →+* T} {g : R →+* S}, f.QuasiFinit
e → g.QuasiFinite → (f.comp g).QuasiFinite
参数：f.comp g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用引理 `Algebra.QuasiFinite.trans`：trans [QuasiFinite R S] [QuasiFinite S T] : Q
uasiFinite R T
· 使用定理 `RingHom.QuasiFinite.toAlgebra`：∀ {R : Type u_1} {S : Type u_2} [inst : C
ommRing R] [inst_1 : CommRing S] {f : R →+* S},   f.QuasiFinite → Algebra.QuasiF
inite R S
-/
lemma QuasiFinite.comp {f : S →+* T} {g : R →+* S} (hf : f.QuasiFinite) (hg : g.QuasiFinite) :
    (f.comp g).QuasiFinite := by
  algebraize [f, g, (f.comp g)]
  exact .trans R S T
/-
**RingHom.QuasiFinite.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.QuasiFinite`。
形式化陈述：∀ {T : Type u_3} [inst : CommRing T] {R : Type u_4} {S : Type u_5} [inst_1
 : CommRing R] [inst_2 : CommRing S]   {f : S →+* T} {g : R →+* S}, (f.comp g).Q
uasiFinite → f.QuasiFinite
参数：f.comp g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用引理 `Algebra.QuasiFinite.of_restrictScalars`：of_restrictScalars [QuasiFinite 
R T] : QuasiFinite S T
· 使用定理 `RingHom.QuasiFinite.toAlgebra`：∀ {R : Type u_1} {S : Type u_2} [inst : C
ommRing R] [inst_1 : CommRing S] {f : R →+* S},   f.QuasiFinite → Algebra.QuasiF
inite R S
-/
lemma QuasiFinite.of_comp {f : S →+* T} {g : R →+* S} (h : (f.comp g).QuasiFinite) :
    f.QuasiFinite := by
  algebraize [f, g, (f.comp g)]
  exact .of_restrictScalars R S T
/-
**RingHom.QuasiFinite.comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.QuasiFinite`。
形式化陈述：∀ {T : Type u_3} [inst : CommRing T] {R : Type u_4} {S : Type u_5} [inst_1
 : CommRing R] [inst_2 : CommRing S]   {f : S →+* T} {g : R →+* S}, g.QuasiFinit
e → ((f.comp g).QuasiFinite ↔ f.QuasiFinite)
参数：(f.comp g).QuasiFinite ↔ f.QuasiFinite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.QuasiFinite.of_comp`：∀ {T : Type u_3} [inst : CommRing T] {R : T
ype u_4} {S : Type u_5} [inst_1 : CommRing R] [inst_2 : CommRing S]   {f : S →+*
 T} {g : R →+* S}…
· 使用定理 `RingHom.QuasiFinite.comp`：∀ {T : Type u_3} [inst : CommRing T] {R : Type
 u_4} {S : Type u_5} [inst_1 : CommRing R] [inst_2 : CommRing S]   {f : S →+* T}
 {g : R →+* S}…
-/
lemma QuasiFinite.comp_iff {f : S →+* T} {g : R →+* S} (hg : g.QuasiFinite) :
    (f.comp g).QuasiFinite ↔ f.QuasiFinite :=
  ⟨.of_comp, (.comp · hg)⟩
/-
**RingHom.QuasiFinite.of_finite** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.QuasiFinite`。
形式化陈述：∀ {T : Type u_3} [inst : CommRing T] {S : Type u_5} [inst_1 : CommRing S] 
{f : S →+* T}, f.Finite → f.QuasiFinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.QuasiFinite.instOfFinite`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Module.Finite R S], 
  Algebra.QuasiFinite …
-/
lemma QuasiFinite.of_finite {f : S →+* T} (hf : f.Finite) : f.QuasiFinite := by
  algebraize [f]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)
/-
**RingHom.QuasiFinite.stableUnderComposition** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.
QuasiFinite`。
形式化陈述：RingHom.StableUnderComposition fun {R S} [CommRing R] [CommRing S] => Ring
Hom.QuasiFinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.QuasiFinite.comp`：∀ {T : Type u_3} [inst : CommRing T] {R : Type
 u_4} {S : Type u_5} [inst_1 : CommRing R] [inst_2 : CommRing S]   {f : S →+* T}
 {g : R →+* S}…
-/
lemma QuasiFinite.stableUnderComposition : StableUnderComposition QuasiFinite :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ comp hg hf
/-
**RingHom.QuasiFinite.respectsIso** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.QuasiFinite
`。
形式化陈述：RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => RingHom.QuasiFi
nite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.StableUnderComposition.respectsIso`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.StableUnd
erComposition P →     (∀ {R S : …
· 使用定理 `RingHom.QuasiFinite.stableUnderComposition`：RingHom.StableUnderCompositi
on fun {R S} [CommRing R] [CommRing S] => RingHom.QuasiFinite
· 使用定理 `RingHom.QuasiFinite.of_finite`：∀ {T : Type u_3} [inst : CommRing T] {S :
 Type u_5} [inst_1 : CommRing S] {f : S →+* T}, f.Finite → f.QuasiFinite
· 使用定理 `RingEquiv.finite`：∀ {A : Type u_1} {B : Type u_2} [inst : CommRing A] [i
nst_1 : CommRing B] (e : A ≃+* B), e.toRingHom.Finite
-/
lemma QuasiFinite.respectsIso : RespectsIso QuasiFinite :=
  stableUnderComposition.respectsIso fun e ↦ .of_finite e.finite
/-
**RingHom.QuasiFinite.isStableUnderBaseChange** 是 Mathlib 中的一个定理，位于命名空间 `RingHom
.QuasiFinite`。
形式化陈述：RingHom.IsStableUnderBaseChange fun {R S} [CommRing R] [CommRing S] => Rin
gHom.QuasiFinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用定理 `RingHom.QuasiFinite.respectsIso`：RingHom.RespectsIso fun {R S} [CommRing
 R] [CommRing S] => RingHom.QuasiFinite
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.quasiFinite_algebraMap`：quasiFinite_algebraMap [Algebra R S] : (
algebraMap R S).QuasiFinite ↔ Algebra.QuasiFinite R S
-/
lemma QuasiFinite.isStableUnderBaseChange : IsStableUnderBaseChange QuasiFinite := by
  refine .mk respectsIso ?_
  introv H
  rw [quasiFinite_algebraMap] at H ⊢
  infer_instance
/-
**RingHom.QuasiFinite.holdsForLocalizationAway** 是 Mathlib 中的一个定理，位于命名空间 `RingHo
m.QuasiFinite`。
形式化陈述：RingHom.HoldsForLocalizationAway fun {R S} [CommRing R] [CommRing S] => Ri
ngHom.QuasiFinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RingHom.quasiFinite_algebraMap`：quasiFinite_algebraMap [Algebra R S] : (
algebraMap R S).QuasiFinite ↔ Algebra.QuasiFinite R S
· 使用引理 `Algebra.QuasiFinite.of_isLocalization`：of_isLocalization (M : Submonoid 
S) [IsLocalization M T] [QuasiFinite R S] : QuasiFinite R T
· 使用定理 `Algebra.QuasiFinite.instOfFinite`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Module.Finite R S], 
  Algebra.QuasiFinite …
-/
lemma QuasiFinite.holdsForLocalizationAway : HoldsForLocalizationAway QuasiFinite := by
  introv R _
  exact quasiFinite_algebraMap.mpr (.of_isLocalization (.powers r))

attribute [local instance high] Algebra.TensorProduct.leftAlgebra Algebra.toModule
    IsScalarTower.right DivisionRing.instIsArtinianRing in
/-
**RingHom.QuasiFinite.ofLocalizationSpanTarget** 是 Mathlib 中的一个定理，位于命名空间 `RingHo
m.QuasiFinite`。
形式化陈述：RingHom.OfLocalizationSpanTarget fun {R S} [CommRing R] [CommRing S] => Ri
ngHom.QuasiFinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.ofLocalizationSpanTarget_iff_finite`：RingHom.ofLocalizationSpanT
arget_iff_finite : RingHom.OfLocalizationSpanTarget @P ↔ RingHom.OfLocalizationF
initeSpanTarget @P
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RingHom.quasiFinite_algebraMap`：quasiFinite_algebraMap [Algebra R S] : (
algebraMap R S).QuasiFinite ↔ Algebra.QuasiFinite R S
· 使用定理 `Algebra.QuasiFinite.finite_fiber`：∀ {R : Type u_1} {S : Type u_2} {inst 
: CommRing R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   [self : Algebra.Qua
siFinite R S] (P : Ide…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `eq_zero_of_localization`：eq_zero_of_localization (r : R) (h : forall (J 
: Ideal R) (_ : J.IsMaximal), algebraMap R (Localization.AtPrime J) r = 0) : r =
 0
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Ideal.primesOver.isPrime`：∀ {A : Type u_2} [inst : CommSemiring A] (p : 
Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p.
primesOver B))…
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 48 条，此处仅展示前 30 条）
-/
lemma QuasiFinite.ofLocalizationSpanTarget : OfLocalizationSpanTarget QuasiFinite := by
  rw [RingHom.ofLocalizationSpanTarget_iff_finite]
  introv R hs H
  algebraize [f]
  refine ⟨fun P _ ↦ ?_⟩
  have (r : s) : Module.Finite P.ResidueField (P.Fiber (Localization.Away r.1)) := by
    have : Algebra.QuasiFinite R (Localization.Away r.1) := quasiFinite_algebraMap.mp (H r)
    infer_instance
  let φ (r : s) : P.Fiber S →ₐ[P.ResidueField] P.Fiber (Localization.Away r.1) :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  let f : P.Fiber S →ₐ[P.ResidueField] Π r : s, (P.Fiber (Localization.Away r.1)) :=
    AlgHom.pi φ
  have : IsNoetherian P.ResidueField (Π r : s, (P.Fiber (Localization.Away r.1))) :=
    isNoetherian_of_isNoetherianRing_of_finite ..
  suffices Function.Injective f from .of_injective f.toLinearMap this
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply eq_zero_of_localization _ fun J hJ ↦ ?_
  let I := (PrimeSpectrum.primesOverOrderIsoFiber R S P).symm ⟨J, inferInstance⟩
  have : ¬ (s : Set S) ⊆ I.1 := fun h ↦
    Ideal.IsPrime.ne_top' (top_le_iff.mp (hs.symm.trans_le (Ideal.span_le.mpr h)))
  obtain ⟨r, hrs, hrI⟩ := Set.not_subset.mp this
  let ψ : P.Fiber (Localization.Away r) →ₐ[P.ResidueField] Localization.AtPrime J :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ⟨IsLocalization.map (M := .powers r)
      (T := J.primeCompl) _ Algebra.TensorProduct.includeRight.toRingHom (by
      simpa [Submonoid.powers_le] using! hrI), by
      simp [IsScalarTower.algebraMap_apply R S (Localization.Away r),
        -Algebra.TensorProduct.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply R _ (Localization.AtPrime J)]⟩ (fun _ _ ↦ .all _ _)
  have hψ : ψ.comp (φ ⟨r, hrs⟩) = IsScalarTower.toAlgHom _ _ _ := by ext; simp [φ, ψ]
  refine congr($hψ a).symm.trans
    (show ψ (f a ⟨r, hrs⟩) = 0 by simp only [ha, Pi.zero_apply, map_zero])
/-
**RingHom.QuasiFinite.propertyIsLocal** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.QuasiFi
nite`。
形式化陈述：RingHom.PropertyIsLocal fun {R S} [CommRing R] [CommRing S] => RingHom.Qua
siFinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.LocalizationPreserves.away`：RingHom.LocalizationPreserves.away (
H : RingHom.LocalizationPreserves @P) : RingHom.LocalizationAwayPreserves P
· 使用引理 `RingHom.IsStableUnderBaseChange.localizationPreserves`：RingHom.IsStableU
nderBaseChange.localizationPreserves : LocalizationPreserves P
· 使用定理 `RingHom.QuasiFinite.isStableUnderBaseChange`：RingHom.IsStableUnderBaseCh
ange fun {R S} [CommRing R] [CommRing S] => RingHom.QuasiFinite
· 使用定理 `RingHom.QuasiFinite.ofLocalizationSpanTarget`：RingHom.OfLocalizationSpan
Target fun {R S} [CommRing R] [CommRing S] => RingHom.QuasiFinite
· 使用定理 `RingHom.OfLocalizationSpanTarget.ofLocalizationSpan`：RingHom.OfLocalizat
ionSpanTarget.ofLocalizationSpan (hP : RingHom.OfLocalizationSpanTarget @P) (hP'
 : RingHom.StableUnderCompositionWithLoca…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAwa
y`：RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway (hP
c : RingHom.StableUnderComposition P) (hPl : HoldsForLocalizati…
· 使用定理 `RingHom.QuasiFinite.stableUnderComposition`：RingHom.StableUnderCompositi
on fun {R S} [CommRing R] [CommRing S] => RingHom.QuasiFinite
· 使用定理 `RingHom.QuasiFinite.holdsForLocalizationAway`：RingHom.HoldsForLocalizati
onAway fun {R S} [CommRing R] [CommRing S] => RingHom.QuasiFinite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma QuasiFinite.propertyIsLocal : PropertyIsLocal QuasiFinite where
  localizationAwayPreserves := isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).left
  StableUnderCompositionWithLocalizationAwayTarget :=
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).right

open TensorProduct in
/-- If `T` is both a finite type `R`-algebra, and the localization of an integral `R`-algebra,
then `T` is quasi-finite over `R` -/
/-
**RingHom.QuasiFinite.of_isIntegral_of_finiteType** 是 Mathlib 中的一个定理，位于命名空间 `Rin
gHom.QuasiFinite`。
形式化陈述：∀ {R : Type u_6} {S : Type u_7} {T : Type u_8} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   {f : R →+* S},   f.IsIntegral → ∀ {g : S 
→+* T}, g.IsStandardOpenImmersion → (g.comp f).FiniteType → (g.comp f).QuasiFini
te
参数：g.comp f；g.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.IsStandardOpenImmersion.exists_away`：∀ (R : Type u_4) (S : Type 
u_5) {inst : CommSemiring R} {inst_1 : CommSemiring S} {inst_2 : Algebra R S}   
[self : Algebra.IsStandardOpenImm…
· 使用定理 `RingHom.IsStandardOpenImmersion.toAlgebra`：∀ {R : Type u_1} {S : Type u_
2} [inst : CommRing R] [inst_1 : CommRing S] {f : R →+* S},   f.IsStandardOpenIm
mersion → Algebra.IsStandardOpe…
· 使用引理 `Algebra.QuasiFinite.of_isIntegral_of_finiteType`：of_isIntegral_of_finite
Type [Algebra.IsIntegral R S] [Algebra.FiniteType R T] (s : S) [IsLocalization.A
way s T] : Algebra.QuasiFinite R T

--- 原说明 ---
If `T` is both a finite type `R`-algebra, and the localization of an integral `R
`-algebra,
then `T` is quasi-finite over `R`
-/
lemma QuasiFinite.of_isIntegral_of_finiteType
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {f : R →+* S} (hf : f.IsIntegral)
    {g : S →+* T} (hg : g.IsStandardOpenImmersion) (hg : (g.comp f).FiniteType) :
    (g.comp f).QuasiFinite := by
  algebraize [f, g, g.comp f]
  obtain ⟨s, hs⟩ := Algebra.IsStandardOpenImmersion.exists_away S T
  exact Algebra.QuasiFinite.of_isIntegral_of_finiteType s

/-- The predicate for a ring hom being quasi-finite at a prime. -/
/-
**RingHom.QuasiFiniteAt** 是 Mathlib 中的一个缩写定义，位于命名空间 `RingHom`。
形式化陈述：QuasiFiniteAt {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) (p : 
Ideal S) [p.IsPrime] : Prop
参数：f : R ->+* S；p : Ideal S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate for a ring hom being quasi-finite at a prime.
-/
abbrev QuasiFiniteAt {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : Ideal S)
    [p.IsPrime] : Prop := letI := f.toAlgebra; Algebra.QuasiFiniteAt R p

end RingHom

