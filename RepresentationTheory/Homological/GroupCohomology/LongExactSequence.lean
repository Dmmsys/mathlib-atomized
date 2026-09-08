/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Long exact sequence in group cohomology

Given a commutative ring `k` and a group `G`, this file shows that a short exact sequence of
`k`-linear `G`-representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` induces a short exact sequence of
complexes
`0 ⟶ inhomogeneousCochains X₁ ⟶ inhomogeneousCochains X₂ ⟶ inhomogeneousCochains X₃ ⟶ 0`.

Since the cohomology of `inhomogeneousCochains Xᵢ` is the group cohomology of `Xᵢ`, this allows us
to specialize API about long exact sequences to group cohomology.

## Main Definitions

* `groupCohomology.δ hX i j hij`: the connecting homomorphism `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` associated
  to an exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations.

## Main Statements

* `groupCohomology.δ_naturality`: naturality of the connecting homomorphism.

-/

public section

universe u v

namespace groupCohomology

open CategoryTheory ShortComplex

variable {k G : Type u} [CommRing k] [Group G]
  {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**groupCohomology.map_cochainsFunctor_shortExact** 是 Mathlib 中的一个引理，位于命名空间 `grou
pCohomology`。
形式化陈述：map_cochainsFunctor_shortExact : ShortExact (X.map (cochainsFunctor k G))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.shortExact_of_degreewise_shortExact`：shortExact_of_de
greewise_shortExact (hS : forall (i : ι), (S.map (eval C c i)).ShortExact) : S.S
hortExact where mono_f
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `groupCohomology.instPreservesZeroMorphismsRepCochainComplexModuleCatNatC
ochainsFunctor`：∀ (k G : Type u) [inst : CommRing k] [inst_1 : Group G], (groupC
ohomology.cochainsFunctor k G).PreservesZeroMorphisms
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
· 使用引理 `LinearMap.range_compLeft`：range_compLeft [AddCommMonoid M] [AddCommMonoi
d M₂] [Module R M] [Module R M₂] (f : M ->ₗ[R] M₂) (I : Type*) : LinearMap.range
 (f.compLeft I…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `LinearMap.ker_compLeft`：ker_compLeft [AddCommMonoid M] [AddCommMonoid M₂
] [Module R M] [Module R M₂] (f : M ->ₗ[R] M₂) (I : Type*) : LinearMap.ker (f.co
mpLeft I) = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
-/
lemma map_cochainsFunctor_shortExact :
    ShortExact (X.map (cochainsFunctor k G)) :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker, LinearMap.range_compLeft,
        LinearMap.ker_compLeft, this]
    mono_f := letI := hX.mono_f; cochainsMap_id_f_map_mono X.f i
    epi_g := letI := hX.epi_g; cochainsMap_id_f_map_epi X.g i }

open HomologicalComplex.HomologySequence

/-- The short complex `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)` associated to an exact
sequence of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
/-
**groupCohomology.mapShortComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)` associated to an exact
sequence of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`.
-/
noncomputable abbrev mapShortComplex₁ {i j : ℕ} (hij : i + 1 = j) :=
  (snakeInput (map_cochainsFunctor_shortExact hX) _ _ hij).L₂'

variable (X) in
/-- The short complex `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
/-
**groupCohomology.mapShortComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)` associated to a short comp
lex of
representations `X₁ ⟶ X₂ ⟶ X₃`.
-/
noncomputable abbrev mapShortComplex₂ (i : ℕ) := X.map (functor k G i)

/-- The short complex `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`. -/
/-
**groupCohomology.mapShortComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`.
-/
noncomputable abbrev mapShortComplex₃ {i j : ℕ} (hij : i + 1 = j) :=
  (snakeInput (map_cochainsFunctor_shortExact hX) _ _ hij).L₁'

/-- Exactness of `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)`. -/
/-
**groupCohomology.mapShortComplex** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exactness of `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)`.
-/
lemma mapShortComplex₁_exact {i j : ℕ} (hij : i + 1 = j) :
    (mapShortComplex₁ hX hij).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₁ i j hij

/-- Exactness of `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)`. -/
/-
**groupCohomology.mapShortComplex** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exactness of `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)`.
-/
lemma mapShortComplex₂_exact (i : ℕ) :
    (mapShortComplex₂ X i).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₂ i

/-- Exactness of `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`. -/
/-
**groupCohomology.mapShortComplex** 是 Mathlib 中的一个引理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exactness of `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`.
-/
lemma mapShortComplex₃_exact {i j : ℕ} (hij : i + 1 = j) :
    (mapShortComplex₃ hX hij).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₃ i j hij

/-- The connecting homomorphism `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. -/
/-
**groupCohomology.** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connecting homomorphism `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` associated to an exact seque
nce
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations.
-/
noncomputable abbrev δ (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology X.X₃ i ⟶ groupCohomology X.X₁ j :=
  (map_cochainsFunctor_shortExact hX).δ i j hij

open Limits
/-
**groupCohomology.epi_** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem epi_δ_of_isZero (n : ℕ) (h : IsZero (groupCohomology X.X₂ (n + 1))) :
    Epi (δ hX n (n + 1) rfl) := SnakeInput.epi_δ _ h
/-
**groupCohomology.mono_** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono_δ_of_isZero (n : ℕ) (h : IsZero (groupCohomology X.X₂ n)) :
    Mono (δ hX n (n + 1) rfl) := SnakeInput.mono_δ _ h
/-
**groupCohomology.isIso_** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isIso_δ_of_isZero (n : ℕ) (h : IsZero (groupCohomology X.X₂ n))
    (hs : IsZero (groupCohomology X.X₂ (n + 1))) :
    IsIso (δ hX n (n + 1) rfl) := SnakeInput.isIso_δ _ h hs

set_option backward.defeqAttrib.useBackward true in
/-- Given an exact sequence of `G`-representations `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0`, this expresses an
`n + 1`-cochain `x : Gⁿ⁺¹ → X₁` such that `f ∘ x ∈ Bⁿ⁺¹(G, X₂)` as a cocycle.
Stated for readability of `δ_apply`. -/
/-
**groupCohomology.cocyclesMkOfCompEqD** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomolo
gy`。
形式化陈述：cocyclesMkOfCompEqD {i j : Nat} {y : (Fin i -> G) -> X.X₂} {x : (Fin j -> 
G) -> X.X₁} (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) : cocycles
 X.X₁ j
参数：Fin i -> G；Fin j -> G；hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an exact sequence of `G`-representations `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0`, this ex
presses an
`n + 1`-cochain `x : Gⁿ⁺¹ → X₁` such that `f ∘ x ∈ Bⁿ⁺¹(G, X₂)` as a cocycle.
Stated for readability of `δ_apply`.
-/
noncomputable abbrev cocyclesMkOfCompEqD {i j : ℕ} {y : (Fin i → G) → X.X₂}
    {x : (Fin j → G) → X.X₁} (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) :
    cocycles X.X₁ j :=
  cocyclesMk x <| by simpa [CochainComplex.of.d] using!
    ((map_cochainsFunctor_shortExact hX).d_eq_zero_of_f_eq_d_apply i j y x
      (by simpa using! hx) (j + 1))
/-
**groupCohomology.** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_apply {i j : ℕ} (hij : i + 1 = j)
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` be an `i`-cocycle for `X₃`
    (z : (Fin i → G) → X.X₃) (hz : (inhomogeneousCochains X.X₃).d i j z = 0)
    -- Let `y` be an `i`-cochain for `X₂` such that `g ∘ y = z`
    (y : (Fin i → G) → X.X₂) (hy : (cochainsMap (MonoidHom.id G) X.g).f i y = z)
    -- Let `x` be an `i + 1`-cochain for `X₁` such that `f ∘ x = d(y)`
    (x : (Fin j → G) → X.X₁) (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) :
    -- Then `x` is an `i + 1`-cocycle and `δ z = x` in `Hⁱ⁺¹(X₁)`.
    δ hX i j hij (π X.X₃ i <| cocyclesMk z (by subst hij; simpa [CochainComplex.of.d] using! hz)) =
      π X.X₁ j (cocyclesMkOfCompEqD hX hx) := by
  exact (map_cochainsFunctor_shortExact hX).δ_apply i j hij z hz y hy x
    (by simpa using! hx) (j + 1) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- Stated for readability of `δ₀_apply`. -/
/-
**groupCohomology.mem_cocycles** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Stated for readability of `δ₀_apply`.
-/
theorem mem_cocycles₁_of_comp_eq_d₀₁
    {y : X.X₂} {x : G → X.X₁} (hx : X.f.hom ∘ x = d₀₁ X.X₂ y) :
    x ∈ cocycles₁ X.X₁ := by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH1, LinearMap.compLeft]

set_option backward.isDefEq.respectTransparency.types false in
/-
**groupCohomology.** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ₀_apply
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z : X₃ᴳ` and `y : X₂` be such that `g(y) = z`.
    (z : X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    -- Let `x` be a 1-cochain for `X₁` such that `f ∘ x = d(y)`.
    (x : G → X.X₁) (hx : X.f.hom ∘ x = d₀₁ X.X₂ y) :
    -- Then `x` is a 1-cocycle and `δ z = x` in `H¹(X₁)`.
    δ hX 0 1 rfl ((H0Iso X.X₃).inv z) = H1π X.X₁ ⟨x, mem_cocycles₁_of_comp_eq_d₀₁ hX hx⟩ := by
  simpa [H0Iso, H1π, ← cocyclesMk₁_eq X.X₁, ← cocyclesMk₀_eq z] using!
    δ_apply hX rfl ((cochainsIso₀ X.X₃).inv z.1) (by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, eq_d₀₁_comp_inv]; simp)
      ((cochainsIso₀ X.X₂).inv y)
    (by ext; simp [← hy, cochainsIso₀]) ((cochainsIso₁ X.X₁).inv x) <| by
      ext g
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, eq_d₀₁_comp_inv]
      simpa [← hx] using! congr_fun (congr($((CommSq.vert_inv
        ⟨cochainsMap_f_1_comp_cochainsIso₁ (MonoidHom.id G) X.f⟩).w) x)) g

set_option backward.isDefEq.respectTransparency false in
/-- Stated for readability of `δ₁_apply`. -/
/-
**groupCohomology.mem_cocycles** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Stated for readability of `δ₁_apply`.
-/
theorem mem_cocycles₂_of_comp_eq_d₁₂
    {y : G → X.X₂} {x : G × G → X.X₁} (hx : X.f.hom ∘ x = d₁₂ X.X₂ y) :
    x ∈ cocycles₂ X.X₁ := by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH2 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH2, LinearMap.compLeft]
/-
**groupCohomology.** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ₁_apply
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` be a 1-cocycle for `X₃` and `y` be a 1-cochain for `X₂` such that `g ∘ y = z`.
    (z : cocycles₁ X.X₃) (y : G → X.X₂) (hy : X.g.hom ∘ y = z)
    -- Let `x` be a 2-cochain for `X₁` such that `f ∘ x = d(y)`.
    (x : G × G → X.X₁) (hx : X.f.hom ∘ x = d₁₂ X.X₂ y) :
    -- Then `x` is a 2-cocycle and `δ z = x` in `H²(X₁)`.
    δ hX 1 2 rfl (H1π X.X₃ z) = H2π X.X₁ ⟨x, mem_cocycles₂_of_comp_eq_d₁₂ hX hx⟩ := by
  simpa [H1π, H2π, ← cocyclesMk₂_eq X.X₁, ← cocyclesMk₁_eq X.X₃] using!
    δ_apply hX rfl ((cochainsIso₁ X.X₃).inv z) (by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, eq_d₁₂_comp_inv]
      simp [cocycles₁.d₁₂_apply z]) ((cochainsIso₁ X.X₂).inv y) (by ext; simp [cochainsIso₁, ← hy])
    ((cochainsIso₂ X.X₁).inv x) <| by
      ext g
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, eq_d₁₂_comp_inv]
      simpa [← hx] using! congr_fun (congr($((CommSq.vert_inv
        ⟨cochainsMap_f_2_comp_cochainsIso₂ (MonoidHom.id G) X.f⟩).w) x)) g

/-- `S.map (cochainsFunctor k G)` is short exact in each degree. -/
/-
**groupCohomology.map_cochainsFunctor_eval_shortExact** 是 Mathlib 中的一个引理，位于命名空间 
`groupCohomology`。
形式化陈述：map_cochainsFunctor_eval_shortExact (n : Nat) : ShortExact (X.map <| cocha
insFunctor k G ⋙ HomologicalComplex.eval (ModuleCat k) (.up Nat) n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.map_of_exact`：∀ {C : Type u_1} {D
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `groupCohomology.instPreservesZeroMorphismsRepCochainComplexModuleCatNatC
ochainsFunctor`：∀ (k G : Type u) [inst : CommRing k] [inst_1 : Group G], (groupC
ohomology.cochainsFunctor k G).PreservesZeroMorphisms
· 使用引理 `groupCohomology.map_cochainsFunctor_shortExact`：map_cochainsFunctor_shor
tExact : ShortExact (X.map (cochainsFunctor k G))
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
`S.map (cochainsFunctor k G)` is short exact in each degree.
-/
lemma map_cochainsFunctor_eval_shortExact (n : ℕ) :
    ShortExact (X.map <| cochainsFunctor k G ⋙ HomologicalComplex.eval (ModuleCat k) (.up ℕ) n) :=
  (map_cochainsFunctor_shortExact hX).map_of_exact (HomologicalComplex.eval ..)

omit hX in
/-- The connecting homomorphism `δ` is actually a natural transformation between
  `groupCohomology.funtor`s. -/
/-
**groupCohomology.** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connecting homomorphism `δ` is actually a natural transformation between
  `groupCohomology.funtor`s.
-/
theorem δ_naturality {X1 X2 : ShortComplex (Rep k G)} (hX1 : X1.ShortExact)
    (hX2 : X2.ShortExact) (F : X1 ⟶ X2) (i j : ℕ) (hij : i + 1 = j) :
    (δ hX1 i j hij) ≫ map (.id G) F.τ₁ j  = map (.id G) F.τ₃ i ≫ δ hX2 i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((cochainsFunctor k G).mapShortComplex.map F)
    (map_cochainsFunctor_shortExact hX1) (map_cochainsFunctor_shortExact hX2) i j hij

end groupCohomology

