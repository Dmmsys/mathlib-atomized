/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Meta properties of essentially of finite type ring homomorphisms
-/

public section

namespace RingHom.EssFiniteType

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-
**RingHom.EssFiniteType.comp** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.EssFiniteType`。
形式化陈述：comp {f : R ->+* S} {g : S ->+* T} (hf : f.EssFiniteType) (hg : g.EssFinit
eType) : (g.comp f).EssFiniteType
参数：hf : f.EssFiniteType；hg : g.EssFiniteType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.EssFiniteType.comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type u_
3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 : A
lgebra R S] [ins…
-/
lemma comp {f : R →+* S} {g : S →+* T} (hf : f.EssFiniteType) (hg : g.EssFiniteType) :
    (g.comp f).EssFiniteType := by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.comp R S T
/-
**RingHom.EssFiniteType.comp_iff** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.EssFiniteTyp
e`。
形式化陈述：comp_iff {f : R ->+* S} {g : S ->+* T} (hf : f.EssFiniteType) : (g.comp f)
.EssFiniteType ↔ g.EssFiniteType
参数：hf : f.EssFiniteType。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.EssFiniteType.comp_iff`：∀ (R : Type u_1) (S : Type u_2) (T : Typ
e u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3
 : Algebra R S] [ins…
-/
lemma comp_iff {f : R →+* S} {g : S →+* T} (hf : f.EssFiniteType) :
    (g.comp f).EssFiniteType ↔ g.EssFiniteType := by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.comp_iff R S T
/-
**RingHom.EssFiniteType.of_comp** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.EssFiniteType
`。
形式化陈述：of_comp (f : R ->+* S) {g : S ->+* T} (h : (g.comp f).EssFiniteType) : g.E
ssFiniteType
参数：f : R ->+* S；h : (g.comp f).EssFiniteType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.EssFiniteType.of_comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type
 u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 
: Algebra R S] [ins…
-/
lemma of_comp (f : R →+* S) {g : S →+* T} (h : (g.comp f).EssFiniteType) :
    g.EssFiniteType := by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.of_comp R S T
/-
**RingHom.EssFiniteType.stableUnderComposition** 是 Mathlib 中的一个引理，位于命名空间 `RingHo
m.EssFiniteType`。
形式化陈述：stableUnderComposition : StableUnderComposition EssFiniteType
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.EssFiniteType.comp`：comp {f : R ->+* S} {g : S ->+* T} (hf : f.E
ssFiniteType) (hg : g.EssFiniteType) : (g.comp f).EssFiniteType
-/
lemma stableUnderComposition : StableUnderComposition EssFiniteType :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hf.comp hg
/-
**RingHom.EssFiniteType.respectsIso** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.EssFinite
Type`。
形式化陈述：respectsIso : RespectsIso EssFiniteType
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.StableUnderComposition.respectsIso`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.StableUnd
erComposition P →     (∀ {R S : …
· 使用引理 `RingHom.EssFiniteType.stableUnderComposition`：stableUnderComposition : S
tableUnderComposition EssFiniteType
· 使用定理 `RingHom.FiniteType.essFiniteType`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] {f : R →+* S}, f.FiniteType → f.EssFiniteTyp
e
· 使用定理 `RingHom.FiniteType.of_surjective`：of_surjective (f : A ->+* B) (hf : Sur
jective f) : f.FiniteType
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
-/
lemma respectsIso : RespectsIso EssFiniteType :=
  stableUnderComposition.respectsIso fun e ↦ (FiniteType.of_surjective _ e.surjective).essFiniteType
/-
**RingHom.EssFiniteType.isStableUnderBaseChange** 是 Mathlib 中的一个引理，位于命名空间 `RingH
om.EssFiniteType`。
形式化陈述：isStableUnderBaseChange : IsStableUnderBaseChange EssFiniteType
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用引理 `RingHom.EssFiniteType.respectsIso`：respectsIso : RespectsIso EssFiniteTy
pe
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.essFiniteType_algebraMap`：essFiniteType_algebraMap {R S : Type*}
 [CommRing R] [CommRing S] [Algebra R S] : (algebraMap R S).EssFiniteType ↔ Alge
bra.EssFiniteType R S
· 使用定理 `Algebra.EssFiniteType.baseChange`：∀ (R : Type u_1) (S : Type u_2) (T : T
ype u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst
_3 : Algebra R S] [ins…
-/
lemma isStableUnderBaseChange : IsStableUnderBaseChange EssFiniteType :=
  .mk respectsIso fun R S T _ _ _ _ _ h ↦ by
    rw [essFiniteType_algebraMap] at h ⊢
    infer_instance
/-
**RingHom.EssFiniteType.holdsForLocalization** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.
EssFiniteType`。
形式化陈述：holdsForLocalization : HoldsForLocalization EssFiniteType
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.essFiniteType_algebraMap`：essFiniteType_algebraMap {R S : Type*}
 [CommRing R] [CommRing S] [Algebra R S] : (algebraMap R S).EssFiniteType ↔ Alge
bra.EssFiniteType R S
· 使用定理 `Algebra.EssFiniteType.of_isLocalization`：∀ {R : Type u_1} (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (M : Submonoid
 R)   [IsLocalization M S], A…
-/
lemma holdsForLocalization : HoldsForLocalization EssFiniteType := by
  introv R _
  rw [essFiniteType_algebraMap]
  exact .of_isLocalization _ M
/-
**RingHom.EssFiniteType.residueFieldMap** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.EssFi
niteType`。
形式化陈述：residueFieldMap {f : R ->+* S} [IsLocalRing R] [IsLocalRing S] [IsLocalHom
 f] (hf : f.EssFiniteType) : (IsLocalRing.ResidueField.map f).EssFiniteType
参数：hf : f.EssFiniteType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.EssFiniteType.of_comp`：of_comp (f : R ->+* S) {g : S ->+* T} (h 
: (g.comp f).EssFiniteType) : g.EssFiniteType
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalRing.ResidueField.map_comp_residue`：map_comp_residue (f : R ->+* 
S) [IsLocalHom f] : (ResidueField.map f).comp (residue R) = (residue S).comp f
· 使用引理 `RingHom.EssFiniteType.comp`：comp {f : R ->+* S} {g : S ->+* T} (hf : f.E
ssFiniteType) (hg : g.EssFiniteType) : (g.comp f).EssFiniteType
· 使用定理 `RingHom.FiniteType.essFiniteType`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] {f : R →+* S}, f.FiniteType → f.EssFiniteTyp
e
· 使用定理 `RingHom.FiniteType.of_surjective`：of_surjective (f : A ->+* B) (hf : Sur
jective f) : f.FiniteType
· 使用引理 `IsLocalRing.residue_surjective`：residue_surjective : Function.Surjective
 (IsLocalRing.residue R)
-/
lemma residueFieldMap {f : R →+* S} [IsLocalRing R] [IsLocalRing S] [IsLocalHom f]
    (hf : f.EssFiniteType) :
    (IsLocalRing.ResidueField.map f).EssFiniteType := by
  refine .of_comp (IsLocalRing.residue R) ?_
  rw [IsLocalRing.ResidueField.map_comp_residue]
  exact .comp hf (FiniteType.of_surjective _ <| IsLocalRing.residue_surjective).essFiniteType

end RingHom.EssFiniteType

