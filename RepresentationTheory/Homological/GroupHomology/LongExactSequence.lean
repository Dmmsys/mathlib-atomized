/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-!
# Long exact sequence in group homology

Given a commutative ring `k` and a group `G`, this file shows that a short exact sequence of
`k`-linear `G`-representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` induces a short exact sequence of
complexes
`0 ⟶ inhomogeneousChains X₁ ⟶ inhomogeneousChains X₂ ⟶ inhomogeneousChains X₃ ⟶ 0`.

Since the homology of `inhomogeneousChains Xᵢ` is the group homology of `Xᵢ`, this allows us
to specialize API about long exact sequences to group homology.

## Main definitions

* `groupHomology.δ hX i j hij`: the connecting homomorphism `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated
  to an exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations.

-/

public section

universe v u

namespace groupHomology

open CategoryTheory ShortComplex Finsupp

variable {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**groupHomology.map_chainsFunctor_shortExact** 是 Mathlib 中的一个引理，位于命名空间 `groupHom
ology`。
形式化陈述：map_chainsFunctor_shortExact : ShortExact (X.map (chainsFunctor k G))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.shortExact_of_degreewise_shortExact`：shortExact_of_de
greewise_shortExact (hS : forall (i : ι), (S.map (eval C c i)).ShortExact) : S.S
hortExact where mono_f
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `groupHomology.instPreservesZeroMorphismsRepChainComplexModuleCatNatChain
sFunctor`：∀ (k G : Type u) [inst : CommRing k] [inst_1 : Group G], (groupHomolog
y.chainsFunctor k G).PreservesZeroMorphisms
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker`：∀ {R : Type u}
 [inst : Ring R] {S : CategoryTheory.ShortComplex (ModuleCat R)},   S.Exact → (M
oduleCat.Hom.hom S.f).range = (ModuleCat.Hom.h…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `Rep.instAdditiveModuleCatForget₂IntertwiningMapVρLinearMapIdCarrier`：∀ (
k : Type u) (G : Type v) [inst : Ring k] [inst_1 : Monoid G],   (CategoryTheory.
forget₂ (Rep.{w, u, v} k G) (ModuleCat k)).Additive
· 使用定理 `CategoryTheory.ShortComplex.Exact.map`：∀ {C : Type u_1} {D : Type u_2} [
inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category
.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u
_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCo
mmMonoid M] [ins…
· 使用引理 `groupHomology.chainsMap_id_f_hom_eq_mapRange`：chainsMap_id_f_hom_eq_mapR
ange {A B : Rep k G} (i : Nat) (φ : A ⟶ B) : ((chainsMap (MonoidHom.id G) φ).f i
).hom = mapRange.linearMap φ.hom.t…
· 使用定理 `Finsupp.range_mapRange_linearMap`：range_mapRange_linearMap (f : M ->ₗ[R]
 N) (hf : LinearMap.ker f = ⊥) (I : Type*) : LinearMap.range (mapRange.linearMap
 (α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Rep.mono_iff_injective`：mono_iff_injective (f : A ⟶ B) : Mono f ↔ Functi
on.Injective f.hom
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.ker_mapRange`：ker_mapRange (f : M ->ₗ[R] N) (I : Type*) : Linear
Map.ker (mapRange.linearMap (α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
-/
lemma map_chainsFunctor_shortExact :
    ShortExact (X.map (chainsFunctor k G)) :=
  letI := hX.mono_f
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker, ker_mapRange,
        range_mapRange_linearMap X.f.hom.toLinearMap (LinearMap.ker_eq_bot.2 <|
        (Rep.mono_iff_injective X.f).1 hX.mono_f), this]
    mono_f := chainsMap_id_f_map_mono X.f i
    epi_g := letI := hX.epi_g; chainsMap_id_f_map_epi X.g i }

open HomologicalComplex.HomologySequence

/-- The short complex  `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁) ⟶ Hⱼ(G, X₂)` associated to an exact sequence
of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
/-
**groupHomology.mapShortComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupHomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex  `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁) ⟶ Hⱼ(G, X₂)` associated to an exact se
quence
of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`.
-/
noncomputable abbrev mapShortComplex₁ {i j : ℕ} (hij : j + 1 = i) :=
  (snakeInput (map_chainsFunctor_shortExact hX) _ _ hij).L₂'

variable (X) in
/-- The short complex `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
/-
**groupHomology.mapShortComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupHomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)` associated to a short comp
lex of
representations `X₁ ⟶ X₂ ⟶ X₃`.
-/
noncomputable abbrev mapShortComplex₂ (i : ℕ) := X.map (functor k G i)

/-- The short complex `Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
/-
**groupHomology.mapShortComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupHomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex `Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated to an exact seq
uence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`.
-/
noncomputable abbrev mapShortComplex₃ {i j : ℕ} (hij : j + 1 = i) :=
  (snakeInput (map_chainsFunctor_shortExact hX) _ _ hij).L₁'

/-- Exactness of `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁) ⟶ Hⱼ(G, X₂)`. -/
/-
**groupHomology.mapShortComplex** 是 Mathlib 中的一个引理，位于命名空间 `groupHomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exactness of `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁) ⟶ Hⱼ(G, X₂)`.
-/
lemma mapShortComplex₁_exact {i j : ℕ} (hij : j + 1 = i) :
    (mapShortComplex₁ hX hij).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₁ i j hij

/-- Exactness of `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)`. -/
/-
**groupHomology.mapShortComplex** 是 Mathlib 中的一个引理，位于命名空间 `groupHomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exactness of `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)`.
-/
lemma mapShortComplex₂_exact (i : ℕ) :
    (mapShortComplex₂ X i).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₂ i

/-- Exactness of `Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)`. -/
/-
**groupHomology.mapShortComplex** 是 Mathlib 中的一个引理，位于命名空间 `groupHomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exactness of `Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)`.
-/
lemma mapShortComplex₃_exact {i j : ℕ} (hij : j + 1 = i) :
    (mapShortComplex₃ hX hij).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₃ i j hij

/-- The connecting homomorphism `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. -/
/-
**groupHomology.** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupHomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connecting homomorphism `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated to an exact seque
nce
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations.
-/
noncomputable abbrev δ (i j : ℕ) (hij : j + 1 = i) :
    groupHomology X.X₃ i ⟶ groupHomology X.X₁ j :=
  (map_chainsFunctor_shortExact hX).δ i j hij

open Limits
/-
**groupHomology.epi_** 是 Mathlib 中的一个定理，位于命名空间 `groupHomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem epi_δ_of_isZero (n : ℕ) (h : IsZero (groupHomology X.X₂ n)) :
    Epi (δ hX (n + 1) n rfl) := SnakeInput.epi_δ _ h
/-
**groupHomology.mono_** 是 Mathlib 中的一个定理，位于命名空间 `groupHomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono_δ_of_isZero (n : ℕ) (h : IsZero (groupHomology X.X₂ (n + 1))) :
    Mono (δ hX (n + 1) n rfl) := SnakeInput.mono_δ _ h
/-
**groupHomology.isIso_** 是 Mathlib 中的一个定理，位于命名空间 `groupHomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isIso_δ_of_isZero (n : ℕ) (hs : IsZero (groupHomology X.X₂ (n + 1)))
    (h : IsZero (groupHomology X.X₂ n)) :
    IsIso (δ hX (n + 1) n rfl) := SnakeInput.isIso_δ _ hs h

set_option backward.isDefEq.respectTransparency false in
/-- Given an exact sequence of `G`-representations `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0`, this expresses an
`n`-chain `x : Gⁿ →₀ X₁` such that `f ∘ x ∈ Bₙ(G, X₂)` as a cycle. Stated for readability of
`δ_apply`. -/
/-
**groupHomology.cyclesMkOfCompEqD** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupHomology`。
形式化陈述：cyclesMkOfCompEqD {i j : Nat} {y : (Fin i -> G) ->₀ X.X₂} {x : (Fin j -> G
) ->₀ X.X₁} (hx : mapRange.linearMap X.f.hom.toLinearMap x = (inhomogeneousChain
s X.X₂).d i j y) : cycles X.X₁ j
参数：Fin i -> G；Fin j -> G；hx : mapRange.linearMap X.f.hom.toLinearMap x = (inhomo
geneousChains X.X₂).d i j y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an exact sequence of `G`-representations `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0`, this ex
presses an
`n`-chain `x : Gⁿ →₀ X₁` such that `f ∘ x ∈ Bₙ(G, X₂)` as a cycle. Stated for re
adability of
`δ_apply`.
-/
noncomputable abbrev cyclesMkOfCompEqD {i j : ℕ} {y : (Fin i → G) →₀ X.X₂}
    {x : (Fin j → G) →₀ X.X₁}
    (hx : mapRange.linearMap X.f.hom.toLinearMap x = (inhomogeneousChains X.X₂).d i j y) :
    cycles X.X₁ j :=
  cyclesMk j _ rfl x <| by
    simpa using! (map_chainsFunctor_shortExact hX).d_eq_zero_of_f_eq_d_apply i j y x
      (by simpa using! hx) _

set_option backward.isDefEq.respectTransparency false in
/-
**groupHomology.** 是 Mathlib 中的一个定理，位于命名空间 `groupHomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_apply {i j : ℕ} (hij : j + 1 = i)
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` be an `j + 1`-cycle for `X₃`
    (z : (Fin i → G) →₀ X.X₃) (hz : (inhomogeneousChains X.X₃).d i j z = 0)
    -- Let `y` be an `j + 1`-chain for `X₂` such that `g ∘ y = z`
    (y : (Fin i → G) →₀ X.X₂) (hy : (chainsMap (MonoidHom.id G) X.g).f i y = z)
    -- Let `x` be an `j`-chain for `X₁` such that `f ∘ x = d(y)`
    (x : (Fin j → G) →₀ X.X₁)
    -- Then `x` is an `j`-cycle and `δ z = x` in `Hⱼ(X₁)`.
    (hx : mapRange.linearMap X.f.hom.toLinearMap x = (inhomogeneousChains X.X₂).d i j y) :
    δ hX i j hij (π X.X₃ i <| cyclesMk i j (by simp [← hij]) z (by simpa using! hz)) =
      π X.X₁ j (cyclesMkOfCompEqD hX hx) := by
  exact (map_chainsFunctor_shortExact hX).δ_apply i j hij z hz y hy x (by simpa using! hx) _ rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**groupHomology.** 是 Mathlib 中的一个定理，位于命名空间 `groupHomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ₀_apply
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` by a 1-cycle for `X₃` and `y` a 1-chain for `X₂` such that `g ∘ y = z`.
    (z : cycles₁ X.X₃) (y : G →₀ X.X₂) (hy : mapRange.linearMap X.g.hom.toLinearMap y = z.1)
    -- Let `x : X₁` be such that `f(x) = d(y)`.
    (x : X.X₁) (hx : X.f.hom x = d₁₀ X.X₂ y) :
    -- Then `δ z = x` in `H₀(X₁)`.
    δ hX 1 0 rfl (H1π X.X₃ z) = H0π X.X₁ x := by
  simpa only [H1π, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, H0π,
    ← cyclesMk₀_eq X.X₁, ← cyclesMk₁_eq X.X₃]
  using! δ_apply hX (i := 1) (j := 0) rfl ((chainsIso₁ X.X₃).inv z.1) (by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, eq_d₁₀_comp_inv]; simp)
    ((chainsIso₁ X.X₂).inv y) (Finsupp.ext fun _ => by simp [chainsIso₁, ← hy])
    ((chainsIso₀ X.X₁).inv x) (Finsupp.ext fun _ => by
      conv_rhs => rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, eq_d₁₀_comp_inv]
      simp [chainsIso₀, ← hx])

set_option backward.isDefEq.respectTransparency false in
/-- Stated for readability of `δ₁_apply`. -/
/-
**groupHomology.mem_cycles** 是 Mathlib 中的一个定理，位于命名空间 `groupHomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Stated for readability of `δ₁_apply`.
-/
theorem mem_cycles₁_of_comp_eq_d₂₁
    {y : G × G →₀ X.X₂} {x : G →₀ X.X₁} (hx : mapRange.linearMap X.f.hom.toLinearMap x =
    d₂₁ X.X₂ y) :
    x ∈ cycles₁ X.X₁ := LinearMap.mem_ker.2 <| (Rep.mono_iff_injective X.f).1 hX.2 <| by
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH1]

set_option backward.isDefEq.respectTransparency.types false in
/-
**groupHomology.** 是 Mathlib 中的一个定理，位于命名空间 `groupHomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ₁_apply
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` by a 2-cycle for `X₃` and `y` a 2-chain for `X₂` such that `g ∘ y = z`.
    (z : cycles₂ X.X₃) (y : G × G →₀ X.X₂) (hy : mapRange.linearMap X.g.hom.toLinearMap y = z.1)
    -- Let `x` be a 1-chain for `X₁` such that `f ∘ x = d(y)`.
    (x : G →₀ X.X₁) (hx : mapRange.linearMap X.f.hom.toLinearMap x = d₂₁ X.X₂ y) :
    -- Then `x` is a 1-cycle and `δ z = x` in `H₁(X₁)`.
    δ hX 2 1 rfl (H2π X.X₃ z) = H1π X.X₁ ⟨x, mem_cycles₁_of_comp_eq_d₂₁ hX hx⟩ := by
  simpa only [H2π, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, H1π,
    ← cyclesMk₂_eq X.X₃, ← cyclesMk₁_eq X.X₁]
  using! δ_apply hX (i := 2) (j := 1) rfl ((chainsIso₂ X.X₃).inv z.1) (by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, eq_d₂₁_comp_inv]; simp)
    ((chainsIso₂ X.X₂).inv y) (Finsupp.ext fun _ => by simp [chainsIso₂, ← hy])
    ((chainsIso₁ X.X₁).inv x) (Finsupp.ext fun _ => by
    conv_rhs => rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, eq_d₂₁_comp_inv]
    simp [← hx, chainsIso₁])

/-- `S.map (chainsFunctor k G)` is short exact in each degree. -/
/-
**groupHomology.map_chainsFunctor_eval_shortExact** 是 Mathlib 中的一个引理，位于命名空间 `gro
upHomology`。
形式化陈述：map_chainsFunctor_eval_shortExact (n : Nat) : ShortExact (X.map <| chainsF
unctor k G ⋙ HomologicalComplex.eval (ModuleCat k) (.down Nat) n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.map_of_exact`：∀ {C : Type u_1} {D
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `groupHomology.instPreservesZeroMorphismsRepChainComplexModuleCatNatChain
sFunctor`：∀ (k G : Type u) [inst : CommRing k] [inst_1 : Group G], (groupHomolog
y.chainsFunctor k G).PreservesZeroMorphisms
· 使用引理 `groupHomology.map_chainsFunctor_shortExact`：map_chainsFunctor_shortExact
 : ShortExact (X.map (chainsFunctor k G))
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `HomologicalComplex.instPreservesFiniteLimitsEvalOfHasFiniteLimits`：∀ {C 
: Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c : Co
mplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `HomologicalComplex.instPreservesFiniteColimitsEvalOfHasFiniteColimits`：∀
 {C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c 
: ComplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `ModuleCat.instHasFiniteColimits`：∀ (R : Type w) [inst : Ring R], Categor
yTheory.Limits.HasFiniteColimits (ModuleCat R)

--- 原说明 ---
`S.map (chainsFunctor k G)` is short exact in each degree.
-/
lemma map_chainsFunctor_eval_shortExact (n : ℕ) :
    ShortExact (X.map <| chainsFunctor k G ⋙ HomologicalComplex.eval (ModuleCat k) (.down ℕ) n) :=
  (map_chainsFunctor_shortExact hX).map_of_exact (HomologicalComplex.eval ..)

end groupHomology

