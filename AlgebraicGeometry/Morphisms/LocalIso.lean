/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalClosure

/-!
# Local isomorphisms

A local isomorphism of schemes is a morphism that is source-locally an open immersion.
-/

public section

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A local isomorphism of schemes is a morphism that is (Zariski-)source-locally an
open immersion. -/
@[mk_iff]
/-
**AlgebraicGeometry.IsLocalIso** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeometry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A local isomorphism of schemes is a morphism that is (Zariski-)source-locally an
open immersion.
-/
class IsLocalIso (f : X ⟶ Y) : Prop where
  exists_isOpenImmersion (x : X) : ∃ (U : X.Opens), x ∈ U ∧ IsOpenImmersion (U.ι ≫ f)

namespace IsLocalIso

variable (f : X ⟶ Y)

/-
**AlgebraicGeometry.IsLocalIso.eq_sourceLocalClosure_isOpenImmersion** 是 Mathlib
 中的一个引理，位于命名空间 `AlgebraicGeometry.IsLocalIso`。
形式化陈述：eq_sourceLocalClosure_isOpenImmersion : @IsLocalIso = sourceLocalClosure I
sOpenImmersion IsOpenImmersion
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.isLocalIso_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f 
: X ⟶ Y),   AlgebraicGeometry.IsLocalIso f ↔     ∀ (x : ↥X), ∃ U, x ∈ U ∧ Algebr
aicGeometry.IsOpenImme…
· 使用引理 `AlgebraicGeometry.sourceLocalClosure.iff_forall_exists`：iff_forall_exist
s [P.RespectsIso] {f : X ⟶ Y} : sourceLocalClosure IsOpenImmersion P f ↔ forall 
(x : X), exists (U : X.Opens), x in U ∧ P (U…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eq_sourceLocalClosure_isOpenImmersion :
    @IsLocalIso = sourceLocalClosure IsOpenImmersion IsOpenImmersion := by
  ext
  rw [isLocalIso_iff, sourceLocalClosure.iff_forall_exists]
/-
**AlgebraicGeometry.IsLocalIso.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsL
ocalIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtSource @IsLocalIso := by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance
/-
**AlgebraicGeometry.IsLocalIso.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsL
ocalIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMultiplicative @IsLocalIso := by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance
/-
**AlgebraicGeometry.IsLocalIso.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsL
ocalIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderBaseChange @IsLocalIso := by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

/-- `IsLocalIso` is weaker than every source-Zariski-local property containing identities. -/
/-
**AlgebraicGeometry.IsLocalIso.le_of_isZariskiLocalAtSource** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.IsLocalIso`。
形式化陈述：le_of_isZariskiLocalAtSource (P : MorphismProperty Scheme.{u}) [P.Contains
Identities] [IsZariskiLocalAtSource P] : @IsLocalIso <= P
参数：P : MorphismProperty Scheme.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsLocalIso.eq_sourceLocalClosure_isOpenImmersion`：eq_s
ourceLocalClosure_isOpenImmersion : @IsLocalIso = sourceLocalClosure IsOpenImmer
sion IsOpenImmersion
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover`：iff_of_openCo
ver : P f ↔ forall i, P (𝒰.f i ≫ f)
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.of_isOpenImmersion`：of_isOpenIm
mersion [P.ContainsIdentities] [IsOpenImmersion f] : P f

--- 原说明 ---
`IsLocalIso` is weaker than every source-Zariski-local property containing ident
ities.
-/
lemma le_of_isZariskiLocalAtSource (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities]
    [IsZariskiLocalAtSource P] : @IsLocalIso ≤ P := by
  intro X Y f hf
  obtain ⟨𝒰, h⟩ := eq_sourceLocalClosure_isOpenImmersion ▸ hf
  rw [IsZariskiLocalAtSource.iff_of_openCover 𝒰 (P := P)]
  exact fun _ ↦ IsZariskiLocalAtSource.of_isOpenImmersion _

set_option backward.isDefEq.respectTransparency false in
/-- `IsLocalIso` is the weakest source-Zariski-local property containing identities. -/
/-
**AlgebraicGeometry.IsLocalIso.eq_iInf** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeome
try.IsLocalIso`。
形式化陈述：eq_iInf : @IsLocalIso = ⨅ (P : MorphismProperty Scheme.{u}) (_ : P.Contain
sIdentities) (_ : IsZariskiLocalAtSource P), P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `AlgebraicGeometry.IsLocalIso.le_of_isZariskiLocalAtSource`：le_of_isZaris
kiLocalAtSource (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities] [IsZari
skiLocalAtSource P] : @IsLocalIso <= P
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `AlgebraicGeometry.IsLocalIso.instIsMultiplicativeScheme`：CategoryTheory.
MorphismProperty.IsMultiplicative @AlgebraicGeometry.IsLocalIso
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `AlgebraicGeometry.IsLocalIso.instIsZariskiLocalAtSource`：AlgebraicGeomet
ry.IsZariskiLocalAtSource @AlgebraicGeometry.IsLocalIso

--- 原说明 ---
`IsLocalIso` is the weakest source-Zariski-local property containing identities.
-/
lemma eq_iInf :
    @IsLocalIso = ⨅ (P : MorphismProperty Scheme.{u}) (_ : P.ContainsIdentities)
      (_ : IsZariskiLocalAtSource P), P := by
  refine le_antisymm ?_ ?_
  · simp only [le_iInf_iff]
    apply le_of_isZariskiLocalAtSource
  · refine iInf_le_of_le @IsLocalIso (iInf_le_of_le inferInstance (iInf_le _ ?_))
    infer_instance

end IsLocalIso

end AlgebraicGeometry

