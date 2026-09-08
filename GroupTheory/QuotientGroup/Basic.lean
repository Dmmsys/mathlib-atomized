/-
Copyright (c) 2018 Kevin Buzzard, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot
-/
-- This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Quotients of groups by normal subgroups

This file develops the basic theory of quotients of groups by normal subgroups. In particular, it
proves Noether's first and second isomorphism theorems.

## Main statements

* `QuotientGroup.quotientKerEquivRange`: Noether's first isomorphism theorem, an explicit
  isomorphism `G/ker φ → range φ` for every group homomorphism `φ : G →* H`.
* `QuotientGroup.quotientInfEquivProdNormalizerQuotient`: Noether's second isomorphism
  theorem, an explicit isomorphism between `H/(H ∩ N)` and `(HN)/N` given a subgroup `H`
  that lies in the normalizer `N_G(N)` of a subgroup `N` of a group `G`.
* `QuotientGroup.quotientQuotientEquivQuotient`: Noether's third isomorphism theorem,
  the canonical isomorphism between `(G / N) / (M / N)` and `G / M`, where `N ≤ M`.
* `QuotientGroup.comapMk'OrderIso`: The correspondence theorem, a lattice
  isomorphism between the lattice of subgroups of `G ⧸ N` and the sublattice
  of subgroups of `G` containing `N`.

## Tags

isomorphism theorems, quotient groups
-/

@[expose] public section

open Function
open scoped Pointwise

universe u v w x
namespace QuotientGroup

variable {G : Type u} [Group G] (N : Subgroup G) [nN : N.Normal] {H : Type v} [Group H]
  {M : Type x} [Monoid M]

open scoped Pointwise in
@[to_additive]
/-
**QuotientGroup.sound** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：sound (U : Set (G ⧸ N)) (g : N.op) : g • (mk' N) ⁻¹' U = (mk' N) ⁻¹' U
参数：U : Set (G ⧸ N)；g : N.op。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem sound (U : Set (G ⧸ N)) (g : N.op) :
    g • (mk' N) ⁻¹' U = (mk' N) ⁻¹' U := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  congr! 1
  exact Quotient.sound ⟨g⁻¹, rfl⟩

-- for commutative groups we don't need normality assumption

local notation " Q " => G ⧸ N

@[to_additive (attr := simp)]
/-
**QuotientGroup.mk_prod** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：mk_prod {G ι : Type*} [CommGroup G] (N : Subgroup G) (s : Finset ι) {f : ι
 -> G} : ((Finset.prod s f : G) : G ⧸ N) = Finset.prod s (fun i => (f i : G ⧸ N)
)
参数：N : Subgroup G；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
-/
theorem mk_prod {G ι : Type*} [CommGroup G] (N : Subgroup G) (s : Finset ι) {f : ι → G} :
    ((Finset.prod s f : G) : G ⧸ N) = Finset.prod s (fun i => (f i : G ⧸ N)) :=
  map_prod (QuotientGroup.mk' N) _ _

@[to_additive QuotientAddGroup.strictMono_comap_prod_map]
/-
**QuotientGroup.strictMono_comap_prod_map** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGro
up`。
形式化陈述：strictMono_comap_prod_map : StrictMono fun H : Subgroup G => (H.comap N.su
btype, H.map (mk' N))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.strictMono_comap_prod_image`：strictMono_comap_prod_image :
 StrictMono fun t : Subgroup α => (t.comap s.subtype, mk (s
-/
theorem strictMono_comap_prod_map :
    StrictMono fun H : Subgroup G ↦ (H.comap N.subtype, H.map (mk' N)) :=
  strictMono_comap_prod_image N

/-- `(G × H) / (A × B)` is in bijection with `G / A × H / B`. -/
@[to_additive (attr := simps) QuotientAddGroup.prodEquiv
/-- `(G × H) / (A × B)` is in bijection with `G / A × H / B`. -/]
/-
**QuotientGroup.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：prodEquiv (A : Subgroup G) (B : Subgroup H) : (G × H) ⧸ (A.prod B) ≃ (G ⧸ 
A) × H ⧸ B where toFun q
参数：A : Subgroup G；B : Subgroup H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prodEquiv (A : Subgroup G) (B : Subgroup H) : (G × H) ⧸ (A.prod B) ≃ (G ⧸ A) × H ⧸ B where
  toFun q := q.liftOn' (fun (g, h) ↦ (g, h))
      (by simp [QuotientGroup.leftRel_apply, Subgroup.mem_prod, QuotientGroup.eq])
  invFun q := q.1.liftOn₂' q.2 (fun g h ↦ (g, h))
    (by simp [QuotientGroup.leftRel_apply, Subgroup.mem_prod, QuotientGroup.eq, ← and_imp])
  left_inv q := q.inductionOn' (by simp)
  right_inv := fun (q₁, q₂) ↦ Quotient.inductionOn₂' q₁ q₂ (by simp)

/-- `(G × H) / (A × B)` is isomorphic to `G / A × H / B`. -/
@[to_additive (attr := simps!) QuotientAddGroup.prodAddEquiv
/-- `(G × H) / (A × B)` is isomorphic to `G / A × H / B`. -/]
/-
**QuotientGroup.prodMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：prodMulEquiv (A : Subgroup G) (B : Subgroup H) [A.Normal] [B.Normal] : (G 
× H) ⧸ (A.prod B) ≃* (G ⧸ A) × H ⧸ B where __
参数：A : Subgroup G；B : Subgroup H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prodMulEquiv (A : Subgroup G) (B : Subgroup H) [A.Normal] [B.Normal] :
    (G × H) ⧸ (A.prod B) ≃* (G ⧸ A) × H ⧸ B where
  __ := prodEquiv A B
  map_mul' q₁ q₂ := Quotient.inductionOn₂' q₁ q₂ (fun _ _ ↦ rfl)

variable (φ : G →* H)

open MonoidHom

/-- The induced map from the quotient by the kernel to the codomain. -/
@[to_additive /-- The induced map from the quotient by the kernel to the codomain. -/]
/-
**QuotientGroup.kerLift** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：kerLift : G ⧸ ker φ ->* H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map from the quotient by the kernel to the codomain.
-/
def kerLift : G ⧸ ker φ →* H :=
  lift _ φ fun _g => mem_ker.mp

@[to_additive (attr := simp)]
/-
**QuotientGroup.kerLift_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：kerLift_mk (g : G) : (kerLift φ) g = φ g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
-/
theorem kerLift_mk (g : G) : (kerLift φ) g = φ g :=
  rfl

@[to_additive]
/-
**QuotientGroup.kerLift_injective** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：kerLift_injective : Injective (kerLift φ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} 
{s₂ : Setoid β} {p : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q₂ 
: Quotient s…
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
-/
theorem kerLift_injective : Injective (kerLift φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ a = φ b) =>
    Quotient.sound' <| by rw [leftRel_apply, mem_ker, φ.map_mul, ← h, φ.map_inv, inv_mul_cancel]

-- Note that `ker φ` isn't definitionally `ker (φ.rangeRestrict)`
-- so there is a bit of annoying code duplication here
/-- The induced map from the quotient by the kernel to the range. -/
@[to_additive /-- The induced map from the quotient by the kernel to the range. -/]
/-
**QuotientGroup.rangeKerLift** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：rangeKerLift : G ⧸ ker φ ->* φ.range
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map from the quotient by the kernel to the range.
-/
def rangeKerLift : G ⧸ ker φ →* φ.range :=
  lift _ φ.rangeRestrict fun g hg => mem_ker.mp <| by rwa [ker_rangeRestrict]

@[to_additive]
/-
**QuotientGroup.rangeKerLift_injective** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`
。
形式化陈述：rangeKerLift_injective : Injective (rangeKerLift φ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} 
{s₂ : Setoid β} {p : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q₂ 
: Quotient s…
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.ker_rangeRestrict`：ker_rangeRestrict (f : G ->* N) : ker (rang
eRestrict f) = ker f
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
-/
theorem rangeKerLift_injective : Injective (rangeKerLift φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ.rangeRestrict a = φ.rangeRestrict b) =>
    Quotient.sound' <| by
      rw [leftRel_apply, ← ker_rangeRestrict, mem_ker, φ.rangeRestrict.map_mul, ← h,
        φ.rangeRestrict.map_inv, inv_mul_cancel]

@[to_additive]
/-
**QuotientGroup.rangeKerLift_surjective** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup
`。
形式化陈述：rangeKerLift_surjective : Surjective (rangeKerLift φ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
-/
theorem rangeKerLift_surjective : Surjective (rangeKerLift φ) := by
  rintro ⟨_, g, rfl⟩
  use mk g
  rfl

/-- **Noether's first isomorphism theorem** (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/
@[to_additive /-- The first isomorphism theorem (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/]
/-
**QuotientGroup.quotientKerEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：quotientKerEquivRange : G ⧸ ker φ ≃* range φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def quotientKerEquivRange : G ⧸ ker φ ≃* range φ :=
  MulEquiv.ofBijective (rangeKerLift φ) ⟨rangeKerLift_injective φ, rangeKerLift_surjective φ⟩

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a homomorphism `φ : G →* H`
with a right inverse `ψ : H → G`. -/
@[to_additive (attr := simps) /-- The canonical isomorphism `G/(ker φ) ≃+ H` induced by a
homomorphism `φ : G →+ H` with a right inverse `ψ : H → G`. -/]
/-
**QuotientGroup.quotientKerEquivOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `Quotie
ntGroup`。
形式化陈述：quotientKerEquivOfRightInverse (ψ : H -> G) (hφ : RightInverse ψ φ) : G ⧸ 
ker φ ≃* H
参数：ψ : H -> G；hφ : RightInverse ψ φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def quotientKerEquivOfRightInverse (ψ : H → G) (hφ : RightInverse ψ φ) : G ⧸ ker φ ≃* H :=
  { kerLift φ with
    toFun := kerLift φ
    invFun := mk ∘ ψ
    left_inv := fun x => kerLift_injective φ (by rw [Function.comp_apply, kerLift_mk, hφ])
    right_inv := hφ }

/-- The canonical isomorphism `G/⊥ ≃* G`. -/
@[to_additive (attr := simps!) /-- The canonical isomorphism `G/⊥ ≃+ G`. -/]
/-
**QuotientGroup.quotientBot** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：quotientBot : G ⧸ (⊥ : Subgroup G) ≃* G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `G/⊥ ≃* G`.
-/
def quotientBot : G ⧸ (⊥ : Subgroup G) ≃* G :=
  quotientKerEquivOfRightInverse (MonoidHom.id G) id fun _x => rfl

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a surjection `φ : G →* H`.

For a `computable` version, see `QuotientGroup.quotientKerEquivOfRightInverse`.
-/
@[to_additive /-- The canonical isomorphism `G/(ker φ) ≃+ H` induced by a surjection `φ : G →+ H`.
For a `computable` version, see `QuotientAddGroup.quotientKerEquivOfRightInverse`. -/]
/-
**QuotientGroup.quotientKerEquivOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Quotient
Group`。
形式化陈述：quotientKerEquivOfSurjective (hφ : Surjective φ) : G ⧸ ker φ ≃* H
参数：hφ : Surjective φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def quotientKerEquivOfSurjective (hφ : Surjective φ) : G ⧸ ker φ ≃* H :=
  quotientKerEquivOfRightInverse φ _ hφ.hasRightInverse.choose_spec

/-- If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic. -/
@[to_additive /-- If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic. -/]
/-
**QuotientGroup.quotientMulEquivOfEq** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：quotientMulEquivOfEq {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) 
: G ⧸ M ≃* G ⧸ N
参数：h : M = N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def quotientMulEquivOfEq {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N :=
  { Subgroup.quotientEquivOfEq h with
    map_mul' := fun q r => Quotient.inductionOn₂' q r fun _g _h => rfl }

@[to_additive (attr := simp)]
/-
**QuotientGroup.quotientMulEquivOfEq_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup
`。
形式化陈述：quotientMulEquivOfEq_mk {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = 
N) (x : G) : QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) = Quotien
tGroup.mk x
参数：h : M = N；x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientMulEquivOfEq_mk {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) (x : G) :
    QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) = QuotientGroup.mk x :=
  rfl

/-- Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`,
then there is a map `A / (A' ⊓ A) →* B / (B' ⊓ B)` induced by the inclusions. -/
@[to_additive /-- Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`, then there is a
map `A / (A' ⊓ A) →+ B / (B' ⊓ B)` induced by the inclusions. -/]
/-
**QuotientGroup.quotientMapSubgroupOfOfLe** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGro
up`。
形式化陈述：quotientMapSubgroupOfOfLe {A' A B' B : Subgroup G} [_hAN : (A'.subgroupOf 
A).Normal] [_hBN : (B'.subgroupOf B).Normal] (h' : A' <= B') (h : A <= B) : A ⧸ 
A'.subgroupOf A ->* B ⧸ B'.subgroupOf B
参数：A'.subgroupOf A；B'.subgroupOf B；h' : A' <= B'；h : A <= B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def quotientMapSubgroupOfOfLe {A' A B' B : Subgroup G} [_hAN : (A'.subgroupOf A).Normal]
    [_hBN : (B'.subgroupOf B).Normal] (h' : A' ≤ B') (h : A ≤ B) :
    A ⧸ A'.subgroupOf A →* B ⧸ B'.subgroupOf B :=
  map _ _ (Subgroup.inclusion h) <| Subgroup.comap_mono h'

@[to_additive (attr := simp)]
/-
**QuotientGroup.quotientMapSubgroupOfOfLe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quotient
Group`。
形式化陈述：quotientMapSubgroupOfOfLe_mk {A' A B' B : Subgroup G} [_hAN : (A'.subgroup
Of A).Normal] [_hBN : (B'.subgroupOf B).Normal] (h' : A' <= B') (h : A <= B) (x 
: A) : quotientMapSubgroupOfOfLe h' h x = ↑(Subgroup.inclusion h x : B)
参数：A'.subgroupOf A；B'.subgroupOf B；h' : A' <= B'；h : A <= B；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientMapSubgroupOfOfLe_mk {A' A B' B : Subgroup G} [_hAN : (A'.subgroupOf A).Normal]
    [_hBN : (B'.subgroupOf B).Normal] (h' : A' ≤ B') (h : A ≤ B) (x : A) :
    quotientMapSubgroupOfOfLe h' h x = ↑(Subgroup.inclusion h x : B) :=
  rfl

/-- Let `A', A, B', B` be subgroups of `G`.
If `A' = B'` and `A = B`, then the quotients `A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic.

Applying this equiv is nicer than rewriting along the equalities, since the type of
`(A'.subgroupOf A : Subgroup A)` depends on `A`.
-/
@[to_additive /-- Let `A', A, B', B` be subgroups of `G`. If `A' = B'` and `A = B`, then the
quotients `A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic. Applying this equiv is nicer than
rewriting along the equalities, since the type of `(A'.addSubgroupOf A : AddSubgroup A)` depends on
`A`. -/]
/-
**QuotientGroup.equivQuotientSubgroupOfOfEq** 是 Mathlib 中的一个定义，位于命名空间 `QuotientG
roup`。
形式化陈述：equivQuotientSubgroupOfOfEq {A' A B' B : Subgroup G} [hAN : (A'.subgroupOf
 A).Normal] [hBN : (B'.subgroupOf B).Normal] (h' : A' = B') (h : A = B) : A ⧸ A'
.subgroupOf A ≃* B ⧸ B'.subgroupOf B
参数：A'.subgroupOf A；B'.subgroupOf B；h' : A' = B'；h : A = B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equivQuotientSubgroupOfOfEq {A' A B' B : Subgroup G} [hAN : (A'.subgroupOf A).Normal]
    [hBN : (B'.subgroupOf B).Normal] (h' : A' = B') (h : A = B) :
    A ⧸ A'.subgroupOf A ≃* B ⧸ B'.subgroupOf B :=
  (quotientMapSubgroupOfOfLe h'.le h.le).toMulEquiv (quotientMapSubgroupOfOfLe h'.ge h.ge)
    (by ext ⟨x, hx⟩; rfl)
    (by ext ⟨x, hx⟩; rfl)

section ZPow

variable {A B C : Type u} [CommGroup A] [CommGroup B] [CommGroup C]
variable (f : A →* B) (g : B →* A) (e : A ≃* B) (d : B ≃* C) (n : ℤ)

/-- The map of quotients by powers of an integer induced by a group homomorphism. -/
@[to_additive /-- The map of quotients by multiples of an integer induced by an additive group
homomorphism. -/]
/-
**QuotientGroup.homQuotientZPowOfHom** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：homQuotientZPowOfHom : A ⧸ (zpowGroupHom n : A ->* A).range ->* B ⧸ (zpowG
roupHom n : B ->* B).range
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def homQuotientZPowOfHom :
    A ⧸ (zpowGroupHom n : A →* A).range →* B ⧸ (zpowGroupHom n : B →* B).range :=
  lift _ ((mk' _).comp f) fun g ⟨h, (hg : h ^ n = g)⟩ =>
    (eq_one_iff _).mpr ⟨f h, by
      simp only [← hg, map_zpow, zpowGroupHom_apply]⟩

@[to_additive (attr := simp)]
/-
**QuotientGroup.homQuotientZPowOfHom_id** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup
`。
形式化陈述：homQuotientZPowOfHom_id : homQuotientZPowOfHom (MonoidHom.id A) n = Monoid
Hom.id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.monoidHom_ext`：monoidHom_ext ⦃f g : G ⧸ N ->* M⦄ (h : f.co
mp (mk' N) = g.comp (mk' N)) : f = g
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
-/
theorem homQuotientZPowOfHom_id : homQuotientZPowOfHom (MonoidHom.id A) n = MonoidHom.id _ :=
  monoidHom_ext _ rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.homQuotientZPowOfHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGro
up`。
形式化陈述：homQuotientZPowOfHom_comp : homQuotientZPowOfHom (f.comp g) n = (homQuotie
ntZPowOfHom f n).comp (homQuotientZPowOfHom g n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.monoidHom_ext`：monoidHom_ext ⦃f g : G ⧸ N ->* M⦄ (h : f.co
mp (mk' N) = g.comp (mk' N)) : f = g
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
-/
theorem homQuotientZPowOfHom_comp :
    homQuotientZPowOfHom (f.comp g) n =
      (homQuotientZPowOfHom f n).comp (homQuotientZPowOfHom g n) :=
  monoidHom_ext _ rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.homQuotientZPowOfHom_comp_of_rightInverse** 是 Mathlib 中的一个定理，位于命
名空间 `QuotientGroup`。
形式化陈述：homQuotientZPowOfHom_comp_of_rightInverse (i : Function.RightInverse g f) 
: (homQuotientZPowOfHom f n).comp (homQuotientZPowOfHom g n) = MonoidHom.id _
参数：i : Function.RightInverse g f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.monoidHom_ext`：monoidHom_ext ⦃f g : G ⧸ N ->* M⦄ (h : f.co
mp (mk' N) = g.comp (mk' N)) : f = g
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem homQuotientZPowOfHom_comp_of_rightInverse (i : Function.RightInverse g f) :
    (homQuotientZPowOfHom f n).comp (homQuotientZPowOfHom g n) = MonoidHom.id _ :=
  monoidHom_ext _ <| MonoidHom.ext fun x => congrArg _ <| i x

/-- The equivalence of quotients by powers of an integer induced by a group isomorphism. -/
@[to_additive /-- The equivalence of quotients by multiples of an integer induced by an additive
group isomorphism. -/]
/-
**QuotientGroup.equivQuotientZPowOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGrou
p`。
形式化陈述：equivQuotientZPowOfEquiv : A ⧸ (zpowGroupHom n : A ->* A).range ≃* B ⧸ (zp
owGroupHom n : B ->* B).range
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equivQuotientZPowOfEquiv :
    A ⧸ (zpowGroupHom n : A →* A).range ≃* B ⧸ (zpowGroupHom n : B →* B).range :=
  MonoidHom.toMulEquiv _ _
    (homQuotientZPowOfHom_comp_of_rightInverse (e.symm : B →* A) (e : A →* B) n e.left_inv)
    (homQuotientZPowOfHom_comp_of_rightInverse (e : A →* B) (e.symm : B →* A) n e.right_inv)
    -- Porting note: had to explicitly coerce the `MulEquiv`s to `MonoidHom`s

@[to_additive (attr := simp)]
/-
**QuotientGroup.equivQuotientZPowOfEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Quotien
tGroup`。
形式化陈述：equivQuotientZPowOfEquiv_refl : MulEquiv.refl (A ⧸ (zpowGroupHom n : A ->*
 A).range) = equivQuotientZPowOfEquiv (MulEquiv.refl A) n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
-/
theorem equivQuotientZPowOfEquiv_refl :
    MulEquiv.refl (A ⧸ (zpowGroupHom n : A →* A).range) =
      equivQuotientZPowOfEquiv (MulEquiv.refl A) n := by
  ext x
  rw [← Quotient.out_eq' x]
  rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.equivQuotientZPowOfEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Quotien
tGroup`。
形式化陈述：equivQuotientZPowOfEquiv_symm : (equivQuotientZPowOfEquiv e n).symm = equi
vQuotientZPowOfEquiv e.symm n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
-/
theorem equivQuotientZPowOfEquiv_symm :
    (equivQuotientZPowOfEquiv e n).symm = equivQuotientZPowOfEquiv e.symm n :=
  rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.equivQuotientZPowOfEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `Quotie
ntGroup`。
形式化陈述：equivQuotientZPowOfEquiv_trans : (equivQuotientZPowOfEquiv e n).trans (equ
ivQuotientZPowOfEquiv d n) = equivQuotientZPowOfEquiv (e.trans d) n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
-/
theorem equivQuotientZPowOfEquiv_trans :
    (equivQuotientZPowOfEquiv e n).trans (equivQuotientZPowOfEquiv d n) =
      equivQuotientZPowOfEquiv (e.trans d) n := by
  ext x
  rw [← Quotient.out_eq' x]
  rfl

end ZPow

section SndIsomorphismThm

open Subgroup

/-- **Noether's second isomorphism theorem**: given a subgroup `N` of `G` and a
subgroup `H` of the normalizer of `N` in `G`,
defines an isomorphism between `H/(H ∩ N)` and `(HN)/N`. -/
@[to_additive /-- Noether's second isomorphism theorem: given a subgroup `N` of `G` and a
subgroup `H` of the normalizer of `N` in `G`,
defines an isomorphism between `H/(H ∩ N)` and `(H + N)/N` -/]
/-
**QuotientGroup.quotientInfEquivProdNormalizerQuotient** 是 Mathlib 中的一个定义，位于命名空间
 `QuotientGroup`。
形式化陈述：quotientInfEquivProdNormalizerQuotient (H N : Subgroup G) (hLE : H <= norm
alizer N) : letI
参数：H N : Subgroup G；hLE : H <= normalizer N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_subgroupOf_sup_of_le_normalizer`：normal_subgroupOf_sup_o
f_le_normalizer {H N : Subgroup G} (hLE : H <= normalizer N) : (N.subgroupOf (H 
⊔ N)).Normal
· 使用定理 `Subgroup.normal_subgroupOf_of_le_normalizer`：normal_subgroupOf_of_le_nor
malizer {H N : Subgroup G} (hLE : H <= normalizer N) : (N.subgroupOf H).Normal
-/
noncomputable def quotientInfEquivProdNormalizerQuotient (H N : Subgroup G)
    (hLE : H ≤ normalizer N) :
    letI := Subgroup.normal_subgroupOf_of_le_normalizer hLE
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
    H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N) :=
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
  -- φ is the natural homomorphism H →* (HN)/N.
  let φ : H →* _ ⧸ N.subgroupOf (H ⊔ N) :=
    (mk' <| N.subgroupOf (H ⊔ N)).comp (inclusion le_sup_left)
  have φ_surjective : Surjective φ := fun x =>
    x.inductionOn' <| by
      rintro ⟨y, hy : y ∈ (H ⊔ N)⟩
      rw [← SetLike.mem_coe] at hy
      rw [coe_mul_of_left_le_normalizer_right H N hLE] at hy
      rcases hy with ⟨h, hh, n, hn, rfl⟩
      simp only [SetLike.mem_coe] at hn
      use ⟨h, hh⟩
      refine Quotient.eq.mpr ?_
      simp [leftRel_apply, inclusion, mem_subgroupOf, hn]
  (quotientMulEquivOfEq (by simp [φ, ← comap_ker])).trans
    (quotientKerEquivOfSurjective φ φ_surjective)

/-- **Noether's second isomorphism theorem**: given two subgroups `H` and `N` of a group `G`,
where `N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(HN)/N`. -/
@[to_additive /-- Noether's second isomorphism theorem: given two subgroups `H` and `N` of a group
`G`, where `N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(H + N)/N`. -/]
/-
**QuotientGroup.quotientInfEquivProdNormalQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Qu
otientGroup`。
形式化陈述：quotientInfEquivProdNormalQuotient (H N : Subgroup G) [hN : N.Normal] : H 
⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N)
参数：H N : Subgroup G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.le_normalizer_of_normal`：le_normalizer_of_normal [H.Normal] : K
 <= normalizer H
-/
noncomputable def quotientInfEquivProdNormalQuotient (H N : Subgroup G) [hN : N.Normal] :
    H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N) :=
  quotientInfEquivProdNormalizerQuotient H N le_normalizer_of_normal

end SndIsomorphismThm

section ThirdIsoThm

variable (M : Subgroup G) [nM : M.Normal]

@[to_additive]
/-
**QuotientGroup.map_normal** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
形式化陈述：map_normal : (M.map (QuotientGroup.mk' N)).Normal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.map`：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} [i
nst_1 : Group N] {H : Subgroup G},   H.Normal → ∀ (f : G →* N), Function.Surject
ive ⇑f → …
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s
-/
instance map_normal : (M.map (QuotientGroup.mk' N)).Normal :=
  nM.map _ mk_surjective

variable (h : N ≤ M)

set_option backward.isDefEq.respectTransparency false in
/-- The map from the third isomorphism theorem for groups: `(G / N) / (M / N) → G / M`. -/
@[to_additive /-- The map from the third isomorphism theorem for additive groups:
`(A / N) / (M / N) → A / M`. -/]
/-
**QuotientGroup.quotientQuotientEquivQuotientAux** 是 Mathlib 中的一个定义，位于命名空间 `Quot
ientGroup`。
形式化陈述：quotientQuotientEquivQuotientAux : (G ⧸ N) ⧸ M.map (mk' N) ->* G ⧸ M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def quotientQuotientEquivQuotientAux : (G ⧸ N) ⧸ M.map (mk' N) →* G ⧸ M :=
  lift (M.map (mk' N)) (map N M (MonoidHom.id G) h)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_ker, map_mk' N M _ _ x]
      exact (QuotientGroup.eq_one_iff _).mpr hx)

@[to_additive (attr := simp)]
/-
**QuotientGroup.quotientQuotientEquivQuotientAux_mk** 是 Mathlib 中的一个定理，位于命名空间 `Q
uotientGroup`。
形式化陈述：quotientQuotientEquivQuotientAux_mk (x : G ⧸ N) : quotientQuotientEquivQuo
tientAux N M h x = QuotientGroup.map N M (MonoidHom.id G) h x
参数：x : G ⧸ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.lift_mk'`：lift_mk' {φ : G ->* M} (HN : N <= φ.ker) (g : G)
 : lift N φ HN (mk g : Q) = φ g
-/
theorem quotientQuotientEquivQuotientAux_mk (x : G ⧸ N) :
    quotientQuotientEquivQuotientAux N M h x = QuotientGroup.map N M (MonoidHom.id G) h x :=
  QuotientGroup.lift_mk' _ _ x

@[to_additive]
/-
**QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk** 是 Mathlib 中的一个定理，位于命名空间
 `QuotientGroup`。
形式化陈述：quotientQuotientEquivQuotientAux_mk_mk (x : G) : quotientQuotientEquivQuot
ientAux N M h (x : G ⧸ N) = x
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.lift_mk'`：lift_mk' {φ : G ->* M} (HN : N <= φ.ker) (g : G)
 : lift N φ HN (mk g : Q) = φ g
-/
theorem quotientQuotientEquivQuotientAux_mk_mk (x : G) :
    quotientQuotientEquivQuotientAux N M h (x : G ⧸ N) = x :=
  QuotientGroup.lift_mk' (M.map (mk' N)) _ x

set_option backward.isDefEq.respectTransparency false in
/-- **Noether's third isomorphism theorem** for groups: `(G / N) / (M / N) ≃* G / M`. -/
@[to_additive
/-- **Noether's third isomorphism theorem** for additive groups: `(A / N) / (M / N) ≃+ A / M`. -/]
/-
**QuotientGroup.quotientQuotientEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Quotien
tGroup`。
形式化陈述：quotientQuotientEquivQuotient : (G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G
 ⧸ M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def quotientQuotientEquivQuotient : (G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M :=
  MonoidHom.toMulEquiv (quotientQuotientEquivQuotientAux N M h)
    (QuotientGroup.map _ _ (QuotientGroup.mk' N) (Subgroup.le_comap_map _ _))
    (by ext; simp)
    (by ext; simp)

end ThirdIsoThm

section CorrespTheorem

-- All these theorems are primed because `QuotientGroup.mk'` is.
set_option linter.docPrime false

@[to_additive]
/-
**QuotientGroup.le_comap_mk'** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：le_comap_mk' (N : Subgroup G) [N.Normal] (H : Subgroup (G ⧸ N)) : N <= Sub
group.comap (QuotientGroup.mk' N) H
参数：N : Subgroup G；H : Subgroup (G ⧸ N)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
· 使用定理 `Subgroup.comap_mono`：comap_mono {f : G ->* N} {K K' : Subgroup N} : K <=
 K' -> comap f K <= comap f K'
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem le_comap_mk' (N : Subgroup G) [N.Normal] (H : Subgroup (G ⧸ N)) :
    N ≤ Subgroup.comap (QuotientGroup.mk' N) H := by
  simpa using Subgroup.comap_mono (f := mk' N) bot_le

@[to_additive (attr := simp)]
/-
**QuotientGroup.comap_map_mk'** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：comap_map_mk' (N H : Subgroup G) [N.Normal] : Subgroup.comap (mk' N) (Subg
roup.map (mk' N) H) = N ⊔ H
参数：N H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.comap_map_eq`：comap_map_eq (H : Subgroup G) : comap f (map f H)
 = H ⊔ f.ker
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_map_mk' (N H : Subgroup G) [N.Normal] :
    Subgroup.comap (mk' N) (Subgroup.map (mk' N) H) = N ⊔ H := by
  simp [Subgroup.comap_map_eq, sup_comm]

/-- The **correspondence theorem**, or lattice theorem,
or fourth isomorphism theorem for multiplicative groups -/
@[to_additive /-- The **correspondence theorem**, or lattice theorem,
  or fourth isomorphism theorem for additive groups -/]
/-
**QuotientGroup.comapMk'OrderIso** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：{G : Type u} → [inst : Group G] → (N : Subgroup G) → [hn : N.Normal] → Sub
group (G ⧸ N) ≃o { H // N ≤ H }
参数：N : Subgroup G；G ⧸ N。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.le_comap_mk'`：le_comap_mk' (N : Subgroup G) [N.Normal] (H 
: Subgroup (G ⧸ N)) : N <= Subgroup.comap (QuotientGroup.mk' N) H
-/
def comapMk'OrderIso (N : Subgroup G) [hn : N.Normal] :
    Subgroup (G ⧸ N) ≃o { H : Subgroup G // N ≤ H } where
  toFun H' := ⟨Subgroup.comap (mk' N) H', le_comap_mk' N _⟩
  invFun H := Subgroup.map (mk' N) H
  left_inv H' := Subgroup.map_comap_eq_self <| by simp
  right_inv := fun ⟨H, hH⟩ => Subtype.ext <| by simpa
  map_rel_iff' := Subgroup.comap_le_comap_of_surjective <| mk'_surjective _

end CorrespTheorem

section trivial

@[to_additive]
/-
**QuotientGroup.subsingleton_quotient_top** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGro
up`。
形式化陈述：subsingleton_quotient_top : Subsingleton (G ⧸ (⊤ : Subgroup G))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subsingleton_quotient_top : Subsingleton (G ⧸ (⊤ : Subgroup G)) := by
  simp

/-- If the quotient by a subgroup gives a singleton then the subgroup is the whole group. -/
@[to_additive /-- If the quotient by an additive subgroup gives a singleton then the additive
subgroup is the whole additive group. -/]
/-
**QuotientGroup.subgroup_eq_top_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Quoti
entGroup`。
形式化陈述：subgroup_eq_top_of_subsingleton (H : Subgroup G) (h : Subsingleton (G ⧸ H)
) : H = ⊤
参数：H : Subgroup G；h : Subsingleton (G ⧸ H)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
theorem subgroup_eq_top_of_subsingleton (H : Subgroup G) (h : Subsingleton (G ⧸ H)) : H = ⊤ :=
  top_unique fun x _ => by
    have : 1⁻¹ * x ∈ H := QuotientGroup.eq.1 (Subsingleton.elim _ _)
    rwa [inv_one, one_mul] at this

end trivial

@[to_additive]
/-
**QuotientGroup.comap_comap_center** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：comap_comap_center {H₁ : Subgroup G} [H₁.Normal] {H₂ : Subgroup (G ⧸ H₁)} 
[H₂.Normal] : ((Subgroup.center ((G ⧸ H₁) ⧸ H₂)).comap (mk' H₂)).comap (mk' H₁) 
= (Subgroup.center (G ⧸ H₂.comap (mk' H₁))).comap (mk' (H₂.comap (mk' H₁)))
参数：G ⧸ H₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Subgroup.normal_comap`：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} 
[inst_1 : Group N] {H : Subgroup N} [nH : H.Normal] (f : G →* N),   (Subgroup.co
map f H).No…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_comap_center {H₁ : Subgroup G} [H₁.Normal] {H₂ : Subgroup (G ⧸ H₁)} [H₂.Normal] :
    ((Subgroup.center ((G ⧸ H₁) ⧸ H₂)).comap (mk' H₂)).comap (mk' H₁) =
      (Subgroup.center (G ⧸ H₂.comap (mk' H₁))).comap (mk' (H₂.comap (mk' H₁))) := by
  ext x
  simp only [mk'_apply, Subgroup.mem_comap, Subgroup.mem_center_iff, forall_mk, ← mk_mul,
    eq_iff_div_mem, mk_div]

open Subgroup in
@[to_additive]
/-
**QuotientGroup._root_.Subgroup.Characteristic.comap_quotient_mk** 是 Mathlib 中的一
个定理，位于命名空间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subgroup.Characteristic.comap_quotient_mk {H : Subgroup G} [hH : H.Characteristic]
    {K : Subgroup (G ⧸ H)} (hK : K.Characteristic) :
    Characteristic (K.comap (mk' H)) :=
  characteristic_iff_comap_eq.mpr fun φ ↦ congr_arg (comap (mk' H))
    (characteristic_iff_comap_eq.mp hK (congr H H φ (characteristic_iff_map_eq.mp hH φ)))

/--
The `MulEquiv` between the kernel of the restriction map to a normal subgroup `H` of homomorphisms
of type `G →* A` and the group of homomorphisms `G ⧸ H →* A`.
-/
@[to_additive
/--
The `AddEquiv` between the kernel of the restriction map to a normal subgroup `H` of homomorphisms
of type `G →+ A` and the group of homomorphisms `G ⧸ H →+ A`.
-/]
/-
**QuotientGroup._root_.MonoidHom.domRestrictHomKerEquiv** 是 Mathlib 中的一个定义，位于命名空
间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.MonoidHom.domRestrictHomKerEquiv (A : Type*) [CommGroup A] (H : Subgroup G) [H.Normal] :
    (MonoidHom.domRestrictHom H A).ker ≃* (G ⧸ H →* A) where
  toFun := fun ⟨f, hf⟩ ↦ QuotientGroup.lift _ f
    (by simpa [mem_ker, domRestrictHom_apply, domRestrict_eq_one_iff] using! hf)
  invFun f := ⟨f.comp (QuotientGroup.mk' H), domRestrict_eq_one_iff.mpr <| le_comap_mk' H f.ker⟩
  map_mul' _ _ := by ext; simp
  left_inv _ := by simp
  right_inv _ := by ext; simp

@[simp]
/-
**QuotientGroup._root_.MonoidHom.domRestrictHomKerEquiv_apply_coe** 是 Mathlib 中的
一个定理，位于命名空间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MonoidHom.domRestrictHomKerEquiv_apply_coe (A : Type*) [CommGroup A] (H : Subgroup G)
    [H.Normal] (f : (MonoidHom.domRestrictHom H A).ker) (g : G) :
    domRestrictHomKerEquiv A H f g = f.val g := rfl

@[simp]
/-
**QuotientGroup._root_.MonoidHom.domRestrictHomKerEquiv_symm_coe_apply** 是 Mathl
ib 中的一个定理，位于命名空间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MonoidHom.domRestrictHomKerEquiv_symm_coe_apply (A : Type*) [CommGroup A]
    (H : Subgroup G) [H.Normal] (f : G ⧸ H →* A) (g : G) :
    ((domRestrictHomKerEquiv A H).symm f).val g = f g := rfl

@[deprecated (since := "2026-07-19")]
alias _root_.MonoidHom.restrictHomKerEquiv := _root_.MonoidHom.domRestrictHomKerEquiv
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrictHomKerEquiv := _root_.AddMonoidHom.domRestrictHomKerEquiv
@[deprecated (since := "2026-07-19")] alias _root_.MonoidHom.restrictHomKerEquiv_apply_coe :=
  _root_.MonoidHom.domRestrictHomKerEquiv_apply_coe
@[deprecated (since := "2026-07-19")] alias _root_.MonoidHom.restrictHomKerEquiv_symm_coe_apply :=
  _root_.MonoidHom.domRestrictHomKerEquiv_symm_coe_apply

end QuotientGroup

namespace QuotientAddGroup

variable {R : Type*} [NonAssocRing R] (N : AddSubgroup R) [N.Normal]

@[simp]
/-
**QuotientAddGroup.mk_nat_mul** 是 Mathlib 中的一个定理，位于命名空间 `QuotientAddGroup`。
形式化陈述：mk_nat_mul (n : Nat) (a : R) : ((n * a : R) : R ⧸ N) = n • ↑a
参数：n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `QuotientAddGroup.mk_nsmul`：∀ {G : Type u_1} [inst : AddGroup G] (N : Add
Subgroup G) [nN : N.Normal] (a : G) (n : ℕ), ↑(n • a) = n • ↑a
-/
theorem mk_nat_mul (n : ℕ) (a : R) : ((n * a : R) : R ⧸ N) = n • ↑a := by
  rw [← nsmul_eq_mul, mk_nsmul N a n]

@[simp]
/-
**QuotientAddGroup.mk_int_mul** 是 Mathlib 中的一个定理，位于命名空间 `QuotientAddGroup`。
形式化陈述：mk_int_mul (n : Int) (a : R) : ((n * a : R) : R ⧸ N) = n • ↑a
参数：n : Int；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `QuotientAddGroup.mk_zsmul`：∀ {G : Type u_1} [inst : AddGroup G] (N : Add
Subgroup G) [nN : N.Normal] (a : G) (n : ℤ), ↑(n • a) = n • ↑a
-/
theorem mk_int_mul (n : ℤ) (a : R) : ((n * a : R) : R ⧸ N) = n • ↑a := by
  rw [← zsmul_eq_mul, mk_zsmul N a n]

end QuotientAddGroup

namespace QuotientGroup

section powMonoidHom

-- TODO: Generalize to arbitrary products of homomorphisms

variable {ι : Type*} (A : ι → Type*) [∀ i, CommGroup (A i)] (n : ℕ)

/-- The isomorphism between the quotient of a product by the image of the `n`th power map
and the product of the quotients by the images of the `n`th power maps on the factors. -/
@[to_additive
  /-- The isomorphism between the quotient of a product by the image of the multiplication-by-`n`
  map and the product of the quotients by the images of the multiplication-by-`n` maps
  on the factors. -/ ]
noncomputable
/-
**QuotientGroup.mulEquivPiModRangePowMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Quotie
ntGroup`。
形式化陈述：mulEquivPiModRangePowMonoidHom : ((i : ι) -> A i) ⧸ (powMonoidHom n).range
 ≃* ((i : ι) -> A i ⧸ (powMonoidHom n).range)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulEquivPiModRangePowMonoidHom :
    ((i : ι) → A i) ⧸ (powMonoidHom n).range ≃* ((i : ι) → A i ⧸ (powMonoidHom n).range) :=
  let φ : ((i : ι) → A i) →* (i : ι) → A i ⧸ (powMonoidHom n).range := {
    toFun x := (x ·)
    map_one' := by simp [Pi.one_def]
    map_mul' x y := by simp [Pi.mul_def]
  }
  liftEquiv (φ := φ) _ (fun y ↦ ⟨fun i ↦ Quotient.out (y i), by simp [φ]⟩) <| by
    ext x : 1
    simpa [φ, funext_iff] using (Classical.skolem (p := fun i a ↦ a ^ n = x i)).symm

@[to_additive (attr := simp)]
/-
**QuotientGroup.mulEquivPiModRangePowMonoidHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `
QuotientGroup`。
形式化陈述：mulEquivPiModRangePowMonoidHom_apply (x : (i : ι) -> A i) : mulEquivPiModR
angePowMonoidHom A n ↑x = fun i => ↑(x i)
参数：x : (i : ι) -> A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
-/
lemma mulEquivPiModRangePowMonoidHom_apply (x : (i : ι) → A i) :
    mulEquivPiModRangePowMonoidHom A n ↑x = fun i ↦ ↑(x i) :=
  rfl

end powMonoidHom

end QuotientGroup

