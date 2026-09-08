/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.Order.BourbakiWitt

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.EqLocus
import Mathlib.Algebra.Module.Torsion.Field

/-!
# The span of a set of vectors, as a submodule

* `Submodule.span s` is defined to be the smallest submodule containing the set `s`.

## Notation

* We introduce the notation `R ∙ v` for the span of a singleton, `Submodule.span R {v}`.  This is
  `\span`, not the same as the scalar multiplication `•`/`\bub`.

-/

@[expose] public section

variable {R R₂ K M M₂ V S : Type*}

namespace Submodule

open Function Set

open scoped Pointwise

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable {x : M} (p p' : Submodule R M)
variable [Semiring R₂] {σ₁₂ : R →+* R₂}
variable [AddCommMonoid M₂] [Module R₂ M₂]

variable {s t : Set M}

/-
**Submodule._root_.AddSubmonoid.toNatSubmodule_closure** 是 Mathlib 中的一个引理，位于命名空间
 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AddSubmonoid.toNatSubmodule_closure (s : Set M) :
    (AddSubmonoid.closure s).toNatSubmodule = .span ℕ s :=
  (Submodule.span_le.mpr AddSubmonoid.subset_closure).antisymm'
    ((Submodule.span ℕ s).toAddSubmonoid.closure_le.mpr Submodule.subset_span)

/-- A version of `Submodule.span_eq` for when the span is by a smaller ring. -/
@[simp]
/-
**Submodule.span_coe_eq_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_coe_eq_restrictScalars [Semiring S] [SMul S R] [Module S M] [IsScalar
Tower S R M] : span S (p : Set M) = p.restrictScalars S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_eq`：span_eq : span R (p : Set M) = p

--- 原说明 ---
A version of `Submodule.span_eq` for when the span is by a smaller ring.
-/
theorem span_coe_eq_restrictScalars [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    span S (p : Set M) = p.restrictScalars S :=
  span_eq (p.restrictScalars S)

include σ₁₂ in
/-- A version of `Submodule.map_span_le` that does not require the `RingHomSurjective`
assumption. -/
/-
**Submodule.image_span_subset** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：image_span_subset (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M) (N : Submodule R₂ M₂) :
 f '' span R s subseteq N ↔ forall m in s, f m in N
参数：f : M ->ₛₗ[σ₁₂] M₂；s : Set M；N : Submodule R₂ M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p

--- 原说明 ---
A version of `Submodule.map_span_le` that does not require the `RingHomSurjectiv
e`
assumption.
-/
theorem image_span_subset (f : M →ₛₗ[σ₁₂] M₂) (s : Set M) (N : Submodule R₂ M₂) :
    f '' span R s ⊆ N ↔ ∀ m ∈ s, f m ∈ N := image_subset_iff.trans <| span_le (p := N.comap f)

include σ₁₂ in
/-
**Submodule.image_span_subset_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：image_span_subset_span (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M) : f '' span R s su
bseteq span R₂ (f '' s)
参数：f : M ->ₛₗ[σ₁₂] M₂；s : Set M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.image_span_subset`：image_span_subset (f : M ->ₛₗ[σ₁₂] M₂) (s :
 Set M) (N : Submodule R₂ M₂) : f '' span R s subseteq N ↔ forall m in s, f m in
 N
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
theorem image_span_subset_span (f : M →ₛₗ[σ₁₂] M₂) (s : Set M) : f '' span R s ⊆ span R₂ (f '' s) :=
  (image_span_subset f s _).2 fun x hx ↦ subset_span ⟨x, hx, rfl⟩
/-
**Submodule.map_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M) : (span 
R s).map f = span R₂ (f '' s)
参数：f : M ->ₛₗ[σ₁₂] M₂；s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_eq_of_le`：span_eq_of_le (h₁ : s subseteq p) (h₂ : p <= sp
an R s) : span R s = p
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Submodule.image_span_subset_span`：image_span_subset_span (f : M ->ₛₗ[σ₁₂
] M₂) (s : Set M) : f '' span R s subseteq span R₂ (f '' s)
-/
theorem map_span [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (s : Set M) :
    (span R s).map f = span R₂ (f '' s) :=
  Eq.symm <| span_eq_of_le _ (Set.image_mono subset_span) (image_span_subset_span f s)

alias _root_.LinearMap.map_span := Submodule.map_span
/-
**Submodule.map_span_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_span_le [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M) (N : 
Submodule R₂ M₂) : map f (span R s) <= N ↔ forall m in s, f m in N
参数：f : M ->ₛₗ[σ₁₂] M₂；s : Set M；N : Submodule R₂ M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.image_span_subset`：image_span_subset (f : M ->ₛₗ[σ₁₂] M₂) (s :
 Set M) (N : Submodule R₂ M₂) : f '' span R s subseteq N ↔ forall m in s, f m in
 N
-/
theorem map_span_le [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (s : Set M) (N : Submodule R₂ M₂) :
    map f (span R s) ≤ N ↔ ∀ m ∈ s, f m ∈ N := image_span_subset f s N

alias _root_.LinearMap.map_span_le := Submodule.map_span_le

/-- See also `Submodule.span_preimage_eq`. -/
/-
**Submodule.span_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_preimage_le (f : M ->ₛₗ[σ₁₂] M₂) (s : Set M₂) : span R (f ⁻¹' s) <= (
span R₂ s).comap f
参数：f : M ->ₛₗ[σ₁₂] M₂；s : Set M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submodule.comap_coe`：comap_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂
) : (comap f p : Set M) = f ⁻¹' p
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s

--- 原说明 ---
See also `Submodule.span_preimage_eq`.
-/
theorem span_preimage_le (f : M →ₛₗ[σ₁₂] M₂) (s : Set M₂) :
    span R (f ⁻¹' s) ≤ (span R₂ s).comap f := by
  rw [span_le, comap_coe]
  exact preimage_mono subset_span

alias _root_.LinearMap.span_preimage_le := Submodule.span_preimage_le

include σ₁₂ in
/-
**Submodule.mapsTo_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mapsTo_span {f : M ->ₛₗ[σ₁₂] M₂} {s : Set M} {t : Set M₂} (h : MapsTo f s 
t) : MapsTo f (span R s) (span R₂ t)
参数：h : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Submodule.span_preimage_le`：span_preimage_le (f : M ->ₛₗ[σ₁₂] M₂) (s : S
et M₂) : span R (f ⁻¹' s) <= (span R₂ s).comap f
-/
theorem mapsTo_span {f : M →ₛₗ[σ₁₂] M₂} {s : Set M} {t : Set M₂} (h : MapsTo f s t) :
    MapsTo f (span R s) (span R₂ t) :=
  (span_mono h).trans (span_preimage_le (σ₁₂ := σ₁₂) f t)

alias _root_.Set.MapsTo.submoduleSpan := mapsTo_span

section

variable {N : Type*} [AddCommMonoid N] [Module R N]

/-
**Submodule.linearMap_eq_iff_of_eq_span** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：linearMap_eq_iff_of_eq_span {V : Submodule R M} (f g : V ->ₗ[R] N) {S : Se
t M} (hV : V = span R S) : f = g ↔ forall (s : S), f ⟨s, by simpa only [hV] usin
g! subset_span (by simp)⟩ = g ⟨s, by simpa only [hV] using! subset_span (by simp
)⟩
参数：f g : V ->ₗ[R] N；hV : V = span R S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
lemma linearMap_eq_iff_of_eq_span {V : Submodule R M} (f g : V →ₗ[R] N)
    {S : Set M} (hV : V = span R S) :
    f = g ↔ ∀ (s : S), f ⟨s, by simpa only [hV] using! subset_span (by simp)⟩ =
      g ⟨s, by simpa only [hV] using! subset_span (by simp)⟩ := by
  constructor
  · rintro rfl _
    rfl
  · intro h
    subst hV
    suffices ∀ (x : M) (hx : x ∈ span R S), f ⟨x, hx⟩ = g ⟨x, hx⟩ by
      ext ⟨x, hx⟩
      exact this x hx
    intro x hx
    induction hx using span_induction with
    | mem x hx => exact h ⟨x, hx⟩
    | zero => erw [map_zero, map_zero]
    | add x y hx hy hx' hy' =>
        erw [f.map_add ⟨x, hx⟩ ⟨y, hy⟩, g.map_add ⟨x, hx⟩ ⟨y, hy⟩]
        rw [hx', hy']
    | smul a x hx hx' =>
        erw [f.map_smul a ⟨x, hx⟩, g.map_smul a ⟨x, hx⟩]
        rw [hx']
/-
**Submodule.linearMap_eq_iff_of_span_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Submodule
`。
形式化陈述：linearMap_eq_iff_of_span_eq_top (f g : M ->ₗ[R] N) {S : Set M} (hM : span 
R S = ⊤) : f = g ↔ forall (s : S), f s = g s
参数：f g : M ->ₗ[R] N；hM : span R S = ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用引理 `Submodule.linearMap_eq_iff_of_eq_span`：linearMap_eq_iff_of_eq_span {V : 
Submodule R M} (f g : V ->ₗ[R] N) {S : Set M} (hV : V = span R S) : f = g ↔ fora
ll (s : S), f ⟨s, by simpa …
-/
lemma linearMap_eq_iff_of_span_eq_top (f g : M →ₗ[R] N)
    {S : Set M} (hM : span R S = ⊤) :
    f = g ↔ ∀ (s : S), f s = g s := by
  convert!
    linearMap_eq_iff_of_eq_span (f.comp (Submodule.subtype _)) (g.comp (Submodule.subtype _))
      hM.symm
  constructor
  · rintro rfl
    rfl
  · intro h
    ext x
    exact DFunLike.congr_fun h ⟨x, by simp⟩
/-
**Submodule.linearMap_eq_zero_iff_of_span_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Subm
odule`。
形式化陈述：linearMap_eq_zero_iff_of_span_eq_top (f : M ->ₗ[R] N) {S : Set M} (hM : sp
an R S = ⊤) : f = 0 ↔ forall (s : S), f s = 0
参数：f : M ->ₗ[R] N；hM : span R S = ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.linearMap_eq_iff_of_span_eq_top`：linearMap_eq_iff_of_span_eq_t
op (f g : M ->ₗ[R] N) {S : Set M} (hM : span R S = ⊤) : f = g ↔ forall (s : S), 
f s = g s
-/
lemma linearMap_eq_zero_iff_of_span_eq_top (f : M →ₗ[R] N)
    {S : Set M} (hM : span R S = ⊤) :
    f = 0 ↔ ∀ (s : S), f s = 0 :=
  linearMap_eq_iff_of_span_eq_top f 0 hM
/-
**Submodule.linearMap_eq_zero_iff_of_eq_span** 是 Mathlib 中的一个引理，位于命名空间 `Submodul
e`。
形式化陈述：linearMap_eq_zero_iff_of_eq_span {V : Submodule R M} (f : V ->ₗ[R] N) {S :
 Set M} (hV : V = span R S) : f = 0 ↔ forall (s : S), f ⟨s, by simpa only [hV] u
sing! subset_span (by simp)⟩ = 0
参数：f : V ->ₗ[R] N；hV : V = span R S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.linearMap_eq_iff_of_eq_span`：linearMap_eq_iff_of_eq_span {V : 
Submodule R M} (f g : V ->ₗ[R] N) {S : Set M} (hV : V = span R S) : f = g ↔ fora
ll (s : S), f ⟨s, by simpa …
-/
lemma linearMap_eq_zero_iff_of_eq_span {V : Submodule R M} (f : V →ₗ[R] N)
    {S : Set M} (hV : V = span R S) :
    f = 0 ↔ ∀ (s : S), f ⟨s, by simpa only [hV] using! subset_span (by simp)⟩ = 0 :=
  linearMap_eq_iff_of_eq_span f 0 hV

end

/-- See `Submodule.span_smul_eq` (in `RingTheory.Ideal.Operations`) for
`span R (r • s) = r • span R s` that holds for arbitrary `r` in a `CommSemiring`. -/
/-
**Submodule.span_smul_eq_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_smul_eq_of_isUnit (s : Set M) (r : R) (hr : IsUnit r) : span R (r • s
) = span R s
参数：s : Set M；r : R；hr : IsUnit r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.span_smul_le`：span_smul_le (s : Set M) (r : R) : span R (r • s
) <= span R s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See `Submodule.span_smul_eq` (in `RingTheory.Ideal.Operations`) for
`span R (r • s) = r • span R s` that holds for arbitrary `r` in a `CommSemiring`
.
-/
theorem span_smul_eq_of_isUnit (s : Set M) (r : R) (hr : IsUnit r) : span R (r • s) = span R s := by
  apply le_antisymm
  · apply span_smul_le
  · convert! span_smul_le (r • s) ((hr.unit⁻¹ :) : R)
    simp [smul_smul]

/-- We can regard `coe_iSup_of_chain` as the statement that `(↑) : (Submodule R M) → Set M` is
Scott continuous for the ω-complete partial order induced by the complete lattice structures. -/
/-
**Submodule.coe_scott_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_scott_continuous : OmegaCompletePartialOrder.ωScottContinuous ((↑) : S
ubmodule R M -> Set M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup`：∀ {α : 
Type u_2} {β : Type u_3} [inst : OmegaCompletePartialOrder α] [inst_1 : OmegaCom
pletePartialOrder β] {f : α → β},   (∃ (hf : Monotone…
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.coe_iSup_of_chain`：coe_iSup_of_chain (a : Nat ->o Submodule R 
M) : (↑(⨆ k, a k) : Set M) = ⋃ k, (a k : Set M)

--- 原说明 ---
We can regard `coe_iSup_of_chain` as the statement that `(↑) : (Submodule R M) →
 Set M` is
Scott continuous for the ω-complete partial order induced by the complete lattic
e structures.
-/
theorem coe_scott_continuous :
    OmegaCompletePartialOrder.ωScottContinuous ((↑) : Submodule R M → Set M) :=
  OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup
    ⟨SetLike.coe_mono, fun _ ↦ coe_iSup_of_chain _⟩

section IsScalarTower

variable (S)

variable [Semiring S] [SMul R S] [Module S M] [IsScalarTower R S M] (p : Submodule R M)

/-- The inclusion of an `R`-submodule into its `S`-span, as an `R`-linear map. -/
/-
**Submodule.inclusionSpan** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_1} →   {M : Type u_4} →     (S : Type u_7) →       [inst : Sem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modul
e R M] →             [inst_3 : Semiring S] →               [inst_4 : SMul R S] →
                 [inst_5 : _root_.Module S M] →                   [inst_6 : IsSc
alarTower R S M] → (p : Submodule R M) → ↥p →ₗ[R] ↥(Submodule.span S ↑p)
参数：S : Type u_7；p : Submodule R M；Submodule.span S ↑p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of an `R`-submodule into its `S`-span, as an `R`-linear map.
-/
@[simps] def inclusionSpan :
    p →ₗ[R] span S (p : Set M) where
  toFun x := ⟨x, subset_span x.property⟩
  map_add' x y := by simp
  map_smul' t x := by simp
/-
**Submodule.injective_inclusionSpan** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：injective_inclusionSpan : Injective (p.inclusionSpan S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.inclusionSpan_apply_coe`：∀ {R : Type u_1} {M : Type u_4} (S : 
Type u_7) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M] [inst_3 : Semir…
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
lemma injective_inclusionSpan :
    Injective (p.inclusionSpan S) := by
  intro x y hxy
  rw [Subtype.ext_iff] at hxy
  simpa using hxy
/-
**Submodule.span_range_inclusionSpan** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：span_range_inclusionSpan : span S (range <| p.inclusionSpan S) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.inclusionSpan_apply_coe`：∀ {R : Type u_1} {M : Type u_4} (S : 
Type u_7) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M] [inst_3 : Semir…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `Submodule.map_subtype_top`：map_subtype_top : map p.subtype (⊤ : Submodul
e R p) = p
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
-/
lemma span_range_inclusionSpan :
    span S (range <| p.inclusionSpan S) = ⊤ := by
  have : (span S (p : Set M)).subtype '' range (inclusionSpan S p) = p := by
    ext; simpa [Subtype.ext_iff] using! fun h ↦ subset_span h
  apply map_injective_of_injective (span S (p : Set M)).injective_subtype
  rw [map_subtype_top, map_span, this]

variable (R s)

/-- If `R` is "smaller" ring than `S` then the span by `R` is smaller than the span by `S`. -/
/-
**Submodule.span_le_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_le_restrictScalars : span R s <= (span S s).restrictScalars R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s

--- 原说明 ---
If `R` is "smaller" ring than `S` then the span by `R` is smaller than the span 
by `S`.
-/
theorem span_le_restrictScalars :
    span R s ≤ (span S s).restrictScalars R :=
  Submodule.span_le.2 Submodule.subset_span

/-- A version of `Submodule.span_le_restrictScalars` with coercions. -/
@[simp]
/-
**Submodule.span_subset_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_subset_span : ↑(span R s) subseteq (span S s : Set M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_le_restrictScalars`：span_le_restrictScalars : span R s <=
 (span S s).restrictScalars R

--- 原说明 ---
A version of `Submodule.span_le_restrictScalars` with coercions.
-/
theorem span_subset_span :
    ↑(span R s) ⊆ (span S s : Set M) :=
  span_le_restrictScalars R S s

/-- Taking the span by a large ring of the span by the small ring is the same as taking the span
by just the large ring. -/
@[simp]
/-
**Submodule.span_span_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_span_of_tower : span S (span R s : Set M) = span S s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submodule.span_subset_span`：span_subset_span : ↑(span R s) subseteq (spa
n S s : Set M)
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s

--- 原说明 ---
Taking the span by a large ring of the span by the small ring is the same as tak
ing the span
by just the large ring.
-/
theorem span_span_of_tower :
    span S (span R s : Set M) = span S s :=
  le_antisymm (span_le.2 <| span_subset_span R S s) (span_mono subset_span)
/-
**Submodule.span_eq_top_of_span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_eq_top_of_span_eq_top (s : Set M) (hs : span R s = ⊤) : span S s = ⊤
参数：s : Set M；hs : span R s = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Submodule.span_le_restrictScalars`：span_le_restrictScalars : span R s <=
 (span S s).restrictScalars R
-/
theorem span_eq_top_of_span_eq_top (s : Set M) (hs : span R s = ⊤) : span S s = ⊤ :=
  le_top.antisymm (hs.ge.trans (span_le_restrictScalars R S s))

set_option backward.isDefEq.respectTransparency false in
variable {R S} in
/-
**Submodule.span_range_inclusion_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：span_range_inclusion_eq_top (p : Submodule R M) (q : Submodule S M) (h₁ : 
p <= q.restrictScalars R) (h₂ : q <= span S p) : span S (range (inclusion h₁)) =
 ⊤
参数：p : Submodule R M；q : Submodule S M；h₁ : p <= q.restrictScalars R；h₂ : q <= s
pan S p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Submodule.range_inclusion`：range_inclusion (p q : Submodule R M) (h : p 
<= q) : range (inclusion h) = comap q.subtype p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.span_coe_eq_restrictScalars`：span_coe_eq_restrictScalars [Semi
ring S] [SMul S R] [Module S M] [IsScalarTower S R M] : span S (p : Set M) = p.r
estrictScalars S
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `Submodule.map_subtype_top`：map_subtype_top : map p.subtype (⊤ : Submodul
e R p) = p
-/
lemma span_range_inclusion_eq_top (p : Submodule R M) (q : Submodule S M)
    (h₁ : p ≤ q.restrictScalars R) (h₂ : q ≤ span S p) :
    span S (range (inclusion h₁)) = ⊤ := by
  suffices (span S (range (inclusion h₁))).map q.subtype = q by
    apply map_injective_of_injective q.injective_subtype
    rw [this, q.map_subtype_top]
  rw [map_span]
  suffices q.subtype '' ((LinearMap.range (inclusion h₁)) : Set <| q.restrictScalars R) = p by
    refine this ▸ le_antisymm ?_ h₂
    simpa using span_mono (R := S) h₁
  ext x
  simpa [range_inclusion] using fun hx ↦ h₁ hx

@[simp]
/-
**Submodule.span_range_inclusion_restrictScalars_eq_top** 是 Mathlib 中的一个定理，位于命名空
间 `Submodule`。
形式化陈述：span_range_inclusion_restrictScalars_eq_top : span S (range (inclusion <| 
span_le_restrictScalars R S s)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.span_range_inclusion_eq_top`：span_range_inclusion_eq_top (p : 
Submodule R M) (q : Submodule S M) (h₁ : p <= q.restrictScalars R) (h₂ : q <= sp
an S p) : span S (range (in…
· 使用定理 `Submodule.span_le_restrictScalars`：span_le_restrictScalars : span R s <=
 (span S s).restrictScalars R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s
-/
theorem span_range_inclusion_restrictScalars_eq_top :
    span S (range (inclusion <| span_le_restrictScalars R S s)) = ⊤ :=
  span_range_inclusion_eq_top _ _ _ <| by simp

end IsScalarTower

/-
**Submodule.span_singleton_eq_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：span_singleton_eq_span_singleton {R M : Type*} [Ring R] [IsDomain R] [AddC
ommGroup M] [Module R M] [Module.IsTorsionFree R M] {x y : M} : (R ∙ x) = (R ∙ y
) ↔ exists z : Rˣ, z • x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `smul_ne_zero_iff`：smul_ne_zero_iff : r • m != 0 ↔ r != 0 ∧ m != 0
· 使用定理 `Submodule.span_singleton_group_smul_eq`：span_singleton_group_smul_eq {G}
 [Group G] [SMul G R] [MulAction G M] [IsScalarTower G R M] (g : G) (x : M) : R 
∙ g • x = R ∙ x
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
-/
theorem span_singleton_eq_span_singleton {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Module.IsTorsionFree R M] {x y : M} :
    (R ∙ x) = (R ∙ y) ↔ ∃ z : Rˣ, z • x = y := by
  constructor
  · simp only [le_antisymm_iff, span_singleton_le_iff_mem, mem_span_singleton]
    rintro ⟨⟨a, rfl⟩, b, hb⟩
    rcases eq_or_ne y 0 with rfl | hy; · simp
    refine ⟨⟨b, a, ?_, ?_⟩, hb⟩
    · apply smul_left_injective R hy
      simpa only [mul_smul, one_smul]
    · rw [← hb] at hy
      apply smul_left_injective R (smul_ne_zero_iff.1 hy).2
      simp only [mul_smul, one_smul, hb]
  · rintro ⟨u, rfl⟩
    exact (span_singleton_group_smul_eq _ _ _).symm

@[simp]
/-
**Submodule.span_image** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) : span R₂ (f '' s)
 = map f (span R s)
参数：f : M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
-/
theorem span_image [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) :
    span R₂ (f '' s) = map f (span R s) :=
  (map_span f s).symm

@[simp]
/-
**Submodule.span_image_linearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_image_linearEquiv {σ₂₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ 
σ₁₂] (f : M ≃ₛₗ[σ₁₂] M₂) : span R₂ (f '' s) = map (f : M ->ₛₗ[σ₁₂] M₂) (span R s
)
参数：f : M ≃ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem span_image_linearEquiv {σ₂₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (f : M ≃ₛₗ[σ₁₂] M₂) : span R₂ (f '' s) = map (f : M →ₛₗ[σ₁₂] M₂) (span R s) :=
  span_image _
/-
**Submodule.apply_mem_span_image_of_mem_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：apply_mem_span_image_of_mem_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] 
M₂) {x : M} {s : Set M} (h : x in Submodule.span R s) : f x in Submodule.span R₂
 (f '' s)
参数：f : M ->ₛₗ[σ₁₂] M₂；h : x in Submodule.span R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
-/
theorem apply_mem_span_image_of_mem_span [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) {x : M}
    {s : Set M} (h : x ∈ Submodule.span R s) : f x ∈ Submodule.span R₂ (f '' s) := by
  rw [Submodule.span_image]
  exact Submodule.mem_map_of_mem h
/-
**Submodule.apply_mem_span_image_iff_mem_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：apply_mem_span_image_iff_mem_span [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂]
 M₂} {x : M} {s : Set M} (hf : Function.Injective f) : f x in Submodule.span R₂ 
(f '' s) ↔ x in Submodule.span R s
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_comap`：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂
} : x in comap f p ↔ f x in p
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Submodule.comap_map_eq_of_injective`：comap_map_eq_of_injective (p : Subm
odule R M) : (p.map f).comap f = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem apply_mem_span_image_iff_mem_span [RingHomSurjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂} {x : M}
    {s : Set M} (hf : Function.Injective f) :
    f x ∈ Submodule.span R₂ (f '' s) ↔ x ∈ Submodule.span R s := by
  rw [← Submodule.mem_comap, ← Submodule.map_span, Submodule.comap_map_eq_of_injective hf]

@[simp]
/-
**Submodule.map_subtype_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_subtype_span_singleton {p : Submodule R M} (x : p) : map p.subtype (R 
∙ x) = R ∙ (x : M)
参数：x : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_subtype_span_singleton {p : Submodule R M} (x : p) :
    map p.subtype (R ∙ x) = R ∙ (x : M) := by simp [← span_image]

/-- `f` is an explicit argument so we can `apply` this theorem and obtain `h` as a new goal. -/
/-
**Submodule.notMem_span_of_apply_notMem_span_image** 是 Mathlib 中的一个定理，位于命名空间 `Su
bmodule`。
形式化陈述：notMem_span_of_apply_notMem_span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ
[σ₁₂] M₂) {x : M} {s : Set M} (h : f x ∉ Submodule.span R₂ (f '' s)) : x ∉ Submo
dule.span R s
参数：f : M ->ₛₗ[σ₁₂] M₂；h : f x ∉ Submodule.span R₂ (f '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Not.imp`：∀ {a b : Prop}, ¬b → (a → b) → ¬a
· 使用定理 `Submodule.apply_mem_span_image_of_mem_span`：apply_mem_span_image_of_mem_
span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) {x : M} {s : Set M} (h : x in 
Submodule.span R s) : f x in Sub…

--- 原说明 ---
`f` is an explicit argument so we can `apply` this theorem and obtain `h` as a n
ew goal.
-/
theorem notMem_span_of_apply_notMem_span_image [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) {x : M}
    {s : Set M} (h : f x ∉ Submodule.span R₂ (f '' s)) : x ∉ Submodule.span R s :=
  h.imp (apply_mem_span_image_of_mem_span f)

section DistribMulAction

variable {α : Type*} [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

/-
**Submodule.smul_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_span (a : α) (s : Set M) : a • span R s = span R (a • s)
参数：a : α；s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
-/
theorem smul_span (a : α) (s : Set M) : a • span R s = span R (a • s) :=
  map_span _ _
/-
**Submodule.smul_def** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：smul_def (a : α) (S : Submodule R M) : a • S = span R (a • S)
参数：a : α；S : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_coe_eq_restrictScalars`：span_coe_eq_restrictScalars [Semi
ring S] [SMul S R] [Module S M] [IsScalarTower S R M] : span S (p : Set M) = p.r
estrictScalars S
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_def (a : α) (S : Submodule R M) : a • S = span R (a • S) := by
  simp [← smul_span]
/-
**Submodule.span_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_smul (a : α) (s : Set M) : span R (a • s) = a • span R s
参数：a : α；s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
-/
theorem span_smul (a : α) (s : Set M) : span R (a • s) = a • span R s :=
  Eq.symm (span_image _).symm
/-
**Submodule.set_smul_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：set_smul_span (s : Set α) (t : Set M) : s • span R t = span R (s • t)
参数：s : Set α；t : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.set_smul_eq_iSup`：set_smul_eq_iSup [SMulCommClass S R M] (s : 
Set S) (N : Submodule R M) : s • N = ⨆ (a in s), a • N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Submodule.smul_span`：smul_span (a : α) (s : Set M) : a • span R s = span
 R (a • s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.iSup_span`：iSup_span {ι : Sort*} (p : ι -> Set M) : ⨆ i, span 
R (p i) = span R (⋃ i, p i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Set.iUnion_smul_set`：iUnion_smul_set (s : Set α) (t : Set β) : ⋃ a in s,
 a • t = s • t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem set_smul_span (s : Set α) (t : Set M) :
    s • span R t = span R (s • t) := by
  simp_rw [set_smul_eq_iSup, smul_span, iSup_span, Set.iUnion_smul_set]
/-
**Submodule.span_set_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_set_smul (s : Set α) (t : Set M) : span R (s • t) = s • span R t
参数：s : Set α；t : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.set_smul_span`：set_smul_span (s : Set α) (t : Set M) : s • spa
n R t = span R (s • t)
-/
theorem span_set_smul (s : Set α) (t : Set M) :
    span R (s • t) = s • span R t := (set_smul_span s t).symm

end DistribMulAction

/-
**Submodule.iSup_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：iSup_toAddSubmonoid {ι : Sort*} (p : ι -> Submodule R M) : (⨆ i, p i).toAd
dSubmonoid = ⨆ i, (p i).toAddSubmonoid
参数：p : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.iSup_eq_span`：iSup_eq_span {ι : Sort*} (p : ι -> Submodule R M
) : ⨆ i, p i = span R (⋃ i, ↑(p i))
· 使用定理 `AddSubmonoid.iSup_eq_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {
ι : Sort u_4} (p : ι → AddSubmonoid M),   ⨆ i, p i = AddSubmonoid.closure (⋃ i, 
↑(p i))
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `AddSubmonoid.subset_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s
 : Set M}, s ⊆ ↑(AddSubmonoid.closure s)
· 使用定理 `AddSubmonoid.zero_mem`：∀ {M : Type u_1} [inst : AddZeroClass M] (S : Add
Submonoid M), 0 ∈ S
· 使用定理 `AddSubmonoid.add_mem`：∀ {M : Type u_1} [inst : AddZeroClass M] (S : AddS
ubmonoid M) {x y : M}, x ∈ S → y ∈ S → x + y ∈ S
· 使用定理 `AddSubmonoid.closure_induction`：∀ {M : Type u_1} [inst : AddZeroClass M]
 {s : Set M} {motive : (x : M) → x ∈ AddSubmonoid.closure s → Prop},   (∀ (x : M
) (h : x ∈ s), motiv…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Submodule.toAddSubmonoid_mono`：toAddSubmonoid_mono : Monotone (toAddSubm
onoid : Submodule R M -> AddSubmonoid M)
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem iSup_toAddSubmonoid {ι : Sort*} (p : ι → Submodule R M) :
    (⨆ i, p i).toAddSubmonoid = ⨆ i, (p i).toAddSubmonoid := by
  refine le_antisymm (fun x => ?_) (iSup_le fun i => toAddSubmonoid_mono <| le_iSup _ i)
  simp_rw [iSup_eq_span, AddSubmonoid.iSup_eq_closure, mem_toAddSubmonoid, coe_toAddSubmonoid]
  intro hx
  refine Submodule.span_induction (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_)
    (fun r x _ hx => ?_) hx
  · exact AddSubmonoid.subset_closure hx
  · exact AddSubmonoid.zero_mem _
  · exact AddSubmonoid.add_mem _ hx hy
  · refine AddSubmonoid.closure_induction ?_ ?_ ?_ hx
    · rintro x ⟨_, ⟨i, rfl⟩, hix : x ∈ p i⟩
      apply AddSubmonoid.subset_closure (Set.mem_iUnion.mpr ⟨i, _⟩)
      exact smul_mem _ r hix
    · rw [smul_zero]
      exact AddSubmonoid.zero_mem _
    · intro x y _ _ hx hy
      rw [smul_add]
      exact AddSubmonoid.add_mem _ hx hy

/-- An induction principle for elements of `⨆ i, p i`.
If `C` holds for `0` and all elements of `p i` for all `i`, and is preserved under addition,
then it holds for all elements of the supremum of `p`. -/
@[elab_as_elim]
/-
**Submodule.iSup_induction** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：iSup_induction {ι : Sort*} (p : ι -> Submodule R M) {motive : M -> Prop} {
x : M} (hx : x in ⨆ i, p i) (mem : forall (i), forall x in p i, motive x) (zero 
: motive 0) (add : forall x y, motive x -> motive y -> motive (x + y)) : motive 
x
参数：p : ι -> Submodule R M；hx : x in ⨆ i, p i；mem : forall (i), forall x in p i, 
motive x；zero : motive 0；add : forall x y, motive x -> motive y -> motive (x + y
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.iSup_induction`：∀ {M : Type u_1} [inst : AddZeroClass M] {ι
 : Sort u_4} (S : ι → AddSubmonoid M) {motive : M → Prop} {x : M},   x ∈ ⨆ i, S 
i →     (∀ (i : ι…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.iSup_toAddSubmonoid`：iSup_toAddSubmonoid {ι : Sort*} (p : ι ->
 Submodule R M) : (⨆ i, p i).toAddSubmonoid = ⨆ i, (p i).toAddSubmonoid
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_toAddSubmonoid`：mem_toAddSubmonoid (p : Submodule R M) (x 
: M) : x in p.toAddSubmonoid ↔ x in p

--- 原说明 ---
An induction principle for elements of `⨆ i, p i`.
If `C` holds for `0` and all elements of `p i` for all `i`, and is preserved und
er addition,
then it holds for all elements of the supremum of `p`.
-/
theorem iSup_induction {ι : Sort*} (p : ι → Submodule R M) {motive : M → Prop} {x : M}
    (hx : x ∈ ⨆ i, p i) (mem : ∀ (i), ∀ x ∈ p i, motive x) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  rw [← mem_toAddSubmonoid, iSup_toAddSubmonoid] at hx
  exact AddSubmonoid.iSup_induction (x := x) _ hx mem zero add

/-- A dependent version of `submodule.iSup_induction`. -/
@[elab_as_elim]
/-
**Submodule.iSup_induction'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：iSup_induction' {ι : Sort*} (p : ι -> Submodule R M) {motive : forall x, (
x in ⨆ i, p i) -> Prop} (mem : forall (i) (x) (hx : x in p i), motive x (mem_iSu
p_of_mem i hx)) (zero : motive 0 (zero_mem _)) (add : forall x y hx hy, motive x
 hx -> motive y hy -> motive (x + y) (add_mem ‹_› ‹_›)) {x : M} (hx : x in ⨆ i, 
p i) : motive x hx
参数：p : ι -> Submodule R M；x in ⨆ i, p i；mem : forall (i) (x) (hx : x in p i), mo
tive x (mem_iSup_of_mem i hx)；zero : motive 0 (zero_mem _)；add : forall x y hx h
y, motive x hx -> motive y hy -> motive (x + y) (add_mem ‹_› ‹_›)；hx : x in ⨆ i,
 p i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Submodule.iSup_induction`：iSup_induction {ι : Sort*} (p : ι -> Submodule
 R M) {motive : M -> Prop} {x : M} (hx : x in ⨆ i, p i) (mem : forall (i), foral
l x in p i, mo…

--- 原说明 ---
A dependent version of `submodule.iSup_induction`.
-/
theorem iSup_induction' {ι : Sort*} (p : ι → Submodule R M) {motive : ∀ x, (x ∈ ⨆ i, p i) → Prop}
    (mem : ∀ (i) (x) (hx : x ∈ p i), motive x (mem_iSup_of_mem i hx)) (zero : motive 0 (zero_mem _))
    (add : ∀ x y hx hy, motive x hx → motive y hy → motive (x + y) (add_mem ‹_› ‹_›)) {x : M}
    (hx : x ∈ ⨆ i, p i) : motive x hx := by
  refine Exists.elim ?_ fun (hx : x ∈ ⨆ i, p i) (hc : motive x hx) => hc
  refine iSup_induction p (motive := fun x : M ↦ ∃ (hx : x ∈ ⨆ i, p i), motive x hx) hx
    (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, mem _ _ hx⟩
  · exact ⟨_, zero⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, add _ _ _ _ Cx Cy⟩
/-
**Submodule.singleton_span_isCompactElement** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
`。
形式化陈述：singleton_span_isCompactElement (x : M) : IsCompactElement (span R {x} : S
ubmodule R M)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le`：isCompactEl
ement_iff_le_of_directed_sSup_le (k : α) : IsCompactElement k ↔ forall s : Set α
, s.Nonempty -> DirectedOn (· <= ·) s -> k <= sSu…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Submodule.mem_sSup_of_directed`：mem_sSup_of_directed {s : Set (Submodule
 R M)} {z} (hs : s.Nonempty) (hdir : DirectedOn (· <= ·) s) : z in sSup s ↔ exis
ts y in s, z in y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem singleton_span_isCompactElement (x : M) :
    IsCompactElement (span R {x} : Submodule R M) := by
  rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le]
  intro d hemp hdir hsup
  have : x ∈ (sSup d) := (SetLike.le_def.mp hsup) (mem_span_singleton_self x)
  obtain ⟨y, ⟨hyd, hxy⟩⟩ := (mem_sSup_of_directed hemp hdir).mp this
  exact ⟨y, ⟨hyd, by simpa only [span_le, singleton_subset_iff] ⟩⟩

/-- The span of a finite subset is compact in the lattice of submodules. -/
/-
**Submodule.finset_span_isCompactElement** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：finset_span_isCompactElement (S : Finset M) : IsCompactElement (span R S :
 Submodule R M)
参数：S : Finset M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_eq_iSup_of_singleton_spans`：span_eq_iSup_of_singleton_spa
ns (s : Set M) : span R s = ⨆ x in s, R ∙ x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `CompleteLattice.isCompactElement_finsetSup`：isCompactElement_finsetSup {
α β : Type*} [CompleteLattice α] {f : β -> α} (s : Finset β) (h : forall x in s,
 IsCompactElement (f x)) : IsCom…
· 使用定理 `Submodule.singleton_span_isCompactElement`：singleton_span_isCompactEleme
nt (x : M) : IsCompactElement (span R {x} : Submodule R M)

--- 原说明 ---
The span of a finite subset is compact in the lattice of submodules.
-/
theorem finset_span_isCompactElement (S : Finset M) :
    IsCompactElement (span R S : Submodule R M) := by
  rw [span_eq_iSup_of_singleton_spans]
  simp only [Finset.mem_coe]
  rw [← Finset.sup_eq_iSup]
  exact
    CompleteLattice.isCompactElement_finsetSup S fun x _ => singleton_span_isCompactElement x

/-- The span of a finite subset is compact in the lattice of submodules. -/
/-
**Submodule.finite_span_isCompactElement** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：finite_span_isCompactElement (S : Set M) (h : S.Finite) : IsCompactElement
 (span R S : Submodule R M)
参数：S : Set M；h : S.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.finset_span_isCompactElement`：finset_span_isCompactElement (S 
: Finset M) : IsCompactElement (span R S : Submodule R M)
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s

--- 原说明 ---
The span of a finite subset is compact in the lattice of submodules.
-/
theorem finite_span_isCompactElement (S : Set M) (h : S.Finite) :
    IsCompactElement (span R S : Submodule R M) :=
  Finite.coe_toFinset h ▸ finset_span_isCompactElement h.toFinset
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCompactlyGenerated (Submodule R M) :=
  ⟨fun s =>
    ⟨(fun x => span R {x}) '' s,
      ⟨fun t ht => by
        rcases (Set.mem_image _ _ _).1 ht with ⟨x, _, rfl⟩
        apply singleton_span_isCompactElement, by
        rw [sSup_eq_iSup, iSup_image, ← span_eq_iSup_of_singleton_spans, span_eq]⟩⟩⟩

variable {M' : Type*} [AddCommMonoid M'] [Module R M'] (q₁ q₁' : Submodule R M')

/-- The product of two submodules is a submodule. -/
/-
**Submodule.prod** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：prod : Submodule R (M × M')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two submodules is a submodule.
-/
def prod : Submodule R (M × M') :=
  { p.toAddSubmonoid.prod q₁.toAddSubmonoid with
    carrier := p ×ˢ q₁
    smul_mem' := by rintro a ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨smul_mem _ a hx, smul_mem _ a hy⟩ }

@[simp]
/-
**Submodule.prod_coe** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_coe : (prod p q₁ : Set (M × M')) = (p : Set M) ×ˢ (q₁ : Set M')
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_coe : (prod p q₁ : Set (M × M')) = (p : Set M) ×ˢ (q₁ : Set M') :=
  rfl

@[simp]
/-
**Submodule.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_prod {p : Submodule R M} {q : Submodule R M'} {x : M × M'} : x in prod
 p q ↔ x.1 in p ∧ x.2 in q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_prod`：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
-/
theorem mem_prod {p : Submodule R M} {q : Submodule R M'} {x : M × M'} :
    x ∈ prod p q ↔ x.1 ∈ p ∧ x.2 ∈ q :=
  Set.mem_prod
/-
**Submodule.span_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_prod_le (s : Set M) (t : Set M') : span R (s ×ˢ t) <= prod (span R s)
 (span R t)
参数：s : Set M；t : Set M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
theorem span_prod_le (s : Set M) (t : Set M') : span R (s ×ˢ t) ≤ prod (span R s) (span R t) :=
  span_le.2 <| Set.prod_mono subset_span subset_span

@[simp]
/-
**Submodule.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_top : (prod ⊤ ⊤ : Submodule R (M × M')) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_top : (prod ⊤ ⊤ : Submodule R (M × M')) = ⊤ := by ext; simp

@[simp]
/-
**Submodule.prod_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_bot : (prod ⊥ ⊥ : Submodule R (M × M')) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_bot : (prod ⊥ ⊥ : Submodule R (M × M')) = ⊥ := by ext ⟨x, y⟩; simp
/-
**Submodule.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_mono {p p' : Submodule R M} {q q' : Submodule R M'} : p <= p' -> q <=
 q' -> prod p q <= prod p' q'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono {p p' : Submodule R M} {q q' : Submodule R M'} :
    p ≤ p' → q ≤ q' → prod p q ≤ prod p' q' :=
  Set.prod_mono

@[simp]
/-
**Submodule.prod_inf_prod** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_inf_prod : prod p q₁ ⊓ prod p' q₁' = prod (p ⊓ p') (q₁ ⊓ q₁')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.prod_inter_prod`：prod_inter_prod : s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ int
er s₂) ×ˢ (t₁ inter t₂)
-/
theorem prod_inf_prod : prod p q₁ ⊓ prod p' q₁' = prod (p ⊓ p') (q₁ ⊓ q₁') :=
  SetLike.coe_injective Set.prod_inter_prod

@[simp]
/-
**Submodule.prod_sup_prod** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_sup_prod : prod p q₁ ⊔ prod p' q₁' = prod (p ⊔ p') (q₁ ⊔ q₁')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Submodule.prod_mono`：prod_mono {p p' : Submodule R M} {q q' : Submodule 
R M'} : p <= p' -> q <= q' -> prod p q <= prod p' q'
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem prod_sup_prod : prod p q₁ ⊔ prod p' q₁' = prod (p ⊔ p') (q₁ ⊔ q₁') := by
  refine le_antisymm
    (sup_le (prod_mono le_sup_left le_sup_left) (prod_mono le_sup_right le_sup_right)) ?_
  simp only [SetLike.le_def, mem_prod, and_imp, Prod.forall]; intro xx yy hxx hyy
  rcases mem_sup.1 hxx with ⟨x, hx, x', hx', rfl⟩
  rcases mem_sup.1 hyy with ⟨y, hy, y', hy', rfl⟩
  exact mem_sup.2 ⟨(x, y), ⟨hx, hy⟩, (x', y'), ⟨hx', hy'⟩, rfl⟩

/-- If a bilinear map takes values in a submodule along two sets, then the same is true along
the span of these sets. -/
/-
**Submodule._root_.LinearMap.BilinMap.apply_apply_mem_of_mem_span** 是 Mathlib 中的
一个引理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a bilinear map takes values in a submodule along two sets, then the same is t
rue along
the span of these sets.
-/
lemma _root_.LinearMap.BilinMap.apply_apply_mem_of_mem_span {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P]
    (P' : Submodule R P) (s : Set M) (t : Set N)
    (B : M →ₗ[R] N →ₗ[R] P) (hB : ∀ x ∈ s, ∀ y ∈ t, B x y ∈ P')
    (x : M) (y : N) (hx : x ∈ span R s) (hy : y ∈ span R t) :
    B x y ∈ P' := by
  induction hx, hy using span_induction₂ with
  | mem_mem u v hu hv => exact hB u hu v hv
  | zero_left v hv => simp
  | zero_right u hu => simp
  | add_left u₁ u₂ v hu₁ hu₂ hv huv₁ huv₂ => simpa using add_mem huv₁ huv₂
  | add_right u v₁ v₂ hu hv₁ hv₂ huv₁ huv₂ => simpa using add_mem huv₁ huv₂
  | smul_left t u v hu hv huv => simpa using Submodule.smul_mem _ _ huv
  | smul_right t u v hu hv huv => simpa using Submodule.smul_mem _ _ huv

@[simp]
/-
**Submodule.biSup_comap_subtype_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：biSup_comap_subtype_eq_top {ι : Type*} (s : Set ι) (p : ι -> Submodule R M
) : ⨆ i in s, (p i).comap (⨆ i in s, p i).subtype = ⊤
参数：s : Set ι；p : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_comap_eq`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} 
{M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用引理 `le_biSup`：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i 
in s) : f i <= ⨆ i in s, f i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map_iSup`：map_iSup {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> 
Submodule R M) : map f (⨆ i, p i) = ⨆ i, map f (p i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `biSup_congr`：biSup_congr {p : ι -> Prop} (h : forall i, p i -> f i = g i
) : ⨆ (i) (_ : p i), f i = ⨆ (i) (_ : p i), g i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
-/
lemma biSup_comap_subtype_eq_top {ι : Type*} (s : Set ι) (p : ι → Submodule R M) :
    ⨆ i ∈ s, (p i).comap (⨆ i ∈ s, p i).subtype = ⊤ := by
  refine eq_top_iff.mpr fun ⟨x, hx⟩ _ ↦ ?_
  suffices x ∈ (⨆ i ∈ s, (p i).comap (⨆ i ∈ s, p i).subtype).map (⨆ i ∈ s, (p i)).subtype by
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp this
    exact hy
  suffices ∀ i ∈ s, (comap (⨆ i ∈ s, p i).subtype (p i)).map (⨆ i ∈ s, p i).subtype = p i by
    simpa only [map_iSup, biSup_congr this]
  intro i hi
  rw [map_comap_eq, range_subtype, inf_eq_right]
  exact le_biSup p hi
/-
**Submodule._root_.LinearMap.exists_ne_zero_of_sSup_eq** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.exists_ne_zero_of_sSup_eq {N : Submodule R M} {f : N →ₛₗ[σ₁₂] M₂}
    (h : f ≠ 0) (s : Set (Submodule R M)) (hs : sSup s = N):
    ∃ m, ∃ h : m ∈ s, f ∘ₛₗ inclusion ((le_sSup h).trans_eq hs) ≠ 0 :=
  have ⟨_, ⟨m, hm, rfl⟩, ne⟩ := LinearMap.exists_ne_zero_of_sSup_eq_top h (comap N.subtype '' s) <|
    by rw [sSup_eq_iSup] at hs; rw [sSup_image, ← hs, biSup_comap_subtype_eq_top]
  ⟨m, hm, fun eq ↦ ne (LinearMap.ext fun x ↦ congr($eq ⟨x, x.2⟩))⟩
/-
**Submodule.span_val_image_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：span_val_image_eq_iff (p : Submodule R M) (s : Set p) : span R (Subtype.va
l '' s) = p ↔ span R s = ⊤
参数：p : Submodule R M；s : Set p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma span_val_image_eq_iff (p : Submodule R M) (s : Set p) :
    span R (Subtype.val '' s) = p ↔ span R s = ⊤ := by
  simp [← (Submodule.map_injective_of_injective p.injective_subtype).eq_iff, Submodule.map_span]
/-
**Submodule.span_range_subtype_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：span_range_subtype_eq_top_iff {ι : Type*} (p : Submodule R M) {s : ι -> M}
 (hs : forall i, s i in p) : span R (Set.range fun i => (⟨s i, hs i⟩ : p)) = ⊤ ↔
 span R (Set.range s) = p
参数：p : Submodule R M；hs : forall i, s i in p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma span_range_subtype_eq_top_iff {ι : Type*} (p : Submodule R M) {s : ι → M}
    (hs : ∀ i, s i ∈ p) :
    span R (Set.range fun i ↦ (⟨s i, hs i⟩ : p)) = ⊤ ↔ span R (Set.range s) = p := by
  simp [← span_val_image_eq_iff, ← Set.range_comp, Function.comp_def]
/-
**Submodule.comap_le_comap_iff_of_le_range** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`
。
形式化陈述：comap_le_comap_iff_of_le_range {f : M ->ₛₗ[σ₁₂] M₂} [RingHomSurjective σ₁₂
] {p q : Submodule R₂ M₂} (hp : p <= LinearMap.range f) : p.comap f <= q.comap f
 ↔ p <= q
参数：hp : p <= LinearMap.range f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Submodule.map_comap_eq_of_le`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type
 u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : Add
CommMonoid M] [ins…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma comap_le_comap_iff_of_le_range {f : M →ₛₗ[σ₁₂] M₂} [RingHomSurjective σ₁₂]
    {p q : Submodule R₂ M₂} (hp : p ≤ LinearMap.range f) :
    p.comap f ≤ q.comap f ↔ p ≤ q := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_comap_eq_of_le hp]
/-
**Submodule.comap_sup_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：comap_sup_of_injective {f : M ->ₛₗ[σ₁₂] M₂} [RingHomSurjective σ₁₂] {p q :
 Submodule R₂ M₂} (hf : Function.Injective f) (hp : p <= LinearMap.range f) (hq 
: q <= LinearMap.range f) : comap f (p ⊔ q) = comap f p ⊔ comap f q
参数：hf : Function.Injective f；hp : p <= LinearMap.range f；hq : q <= LinearMap.ran
ge f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_sup`：map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f
 p ⊔ map f p'
· 使用定理 `Submodule.map_comap_eq_self`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type 
u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddC
ommMonoid M] [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma comap_sup_of_injective {f : M →ₛₗ[σ₁₂] M₂} [RingHomSurjective σ₁₂] {p q : Submodule R₂ M₂}
    (hf : Function.Injective f) (hp : p ≤ LinearMap.range f) (hq : q ≤ LinearMap.range f) :
    comap f (p ⊔ q) = comap f p ⊔ comap f q := by
  apply map_injective_of_injective hf
  rw [map_sup, map_comap_eq_self, map_comap_eq_self hp, map_comap_eq_self hq]
  simp [sup_le_iff, hp, hq]

end AddCommMonoid

section AddCommGroup

variable {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]

/-
**Submodule.sup_inf_assoc_of_le_of_neg_le** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：sup_inf_assoc_of_le_of_neg_le {s : Submodule R M} (t : Submodule R M) {p :
 Submodule R M} (hsp : s <= p) (hnsp : -s <= p) : (s ⊔ t) ⊓ p = s ⊔ (t ⊓ p)
参数：t : Submodule R M；hsp : s <= p；hnsp : -s <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.neg_le`：neg_le {S T : Submodule R M} : -S <= T ↔ S <= -T
-/
lemma sup_inf_assoc_of_le_of_neg_le {s : Submodule R M} (t : Submodule R M)
    {p : Submodule R M} (hsp : s ≤ p) (hnsp : -s ≤ p) :
    (s ⊔ t) ⊓ p = s ⊔ (t ⊓ p) := by
  ext x; simp only [mem_sup, mem_inf]
  constructor
  · rintro ⟨⟨y, hy, z, hz, hyzx⟩, hx⟩
    refine ⟨y, hy, z, ⟨hz, ?_⟩, hyzx⟩
    rw [← add_right_inj, neg_add_cancel_left] at hyzx
    simpa [hyzx] using p.add_mem (neg_le.mp hnsp hy) hx
  · rintro ⟨y, hy, z, ⟨hz, hz'⟩, hyzx⟩
    refine ⟨⟨y, hy, z, hz, hyzx⟩, ?_⟩
    simpa [← hyzx] using p.add_mem (hsp hy) hz'
/-
**Submodule.inf_sup_assoc_of_le_of_neg_le** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：inf_sup_assoc_of_le_of_neg_le {s : Submodule R M} (t : Submodule R M) {p :
 Submodule R M} (hps : p <= s) (hnps : -p <= s) : (s ⊓ t) ⊔ p = s ⊓ (t ⊔ p)
参数：t : Submodule R M；hps : p <= s；hnps : -p <= s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.sup_inf_assoc_of_le_of_neg_le`：sup_inf_assoc_of_le_of_neg_le {
s : Submodule R M} (t : Submodule R M) {p : Submodule R M} (hsp : s <= p) (hnsp 
: -s <= p) : (s ⊔ t) ⊓ p = s …
-/
lemma inf_sup_assoc_of_le_of_neg_le {s : Submodule R M} (t : Submodule R M)
    {p : Submodule R M} (hps : p ≤ s) (hnps : -p ≤ s) :
    (s ⊓ t) ⊔ p = s ⊓ (t ⊔ p) := by
  rw [sup_comm, inf_comm, ← sup_inf_assoc_of_le_of_neg_le t hps hnps, inf_comm, sup_comm]
/-
**Submodule.span_neg_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_neg_eq_neg (s : Set M) : span R (-s) = -span R s
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submodule.coe_set_neg`：coe_set_neg (S : Submodule R M) : ↑(-S) = -(S : S
et M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.neg_subset`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s t : Set α},
 -s ⊆ t ↔ s ⊆ -t
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Submodule.neg_le`：neg_le {S T : Submodule R M} : -S <= T ↔ S <= -T
-/
theorem span_neg_eq_neg (s : Set M) : span R (-s) = -span R s := by
  apply le_antisymm
  · rw [span_le, coe_set_neg, ← Set.neg_subset, neg_neg]
    exact subset_span
  · rw [neg_le, span_le, coe_set_neg, ← Set.neg_subset]
    exact subset_span

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
/-
**Submodule._root_.AddSubgroup.toIntSubmodule_closure** 是 Mathlib 中的一个引理，位于命名空间 
`Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AddSubgroup.toIntSubmodule_closure (s : Set M) :
    (AddSubgroup.closure s).toIntSubmodule = .span ℤ s :=
  (Submodule.span_le.mpr AddSubgroup.subset_closure).antisymm'
    ((Submodule.span ℤ s).toAddSubgroup.closure_le.mpr Submodule.subset_span)

@[simp]
/-
**Submodule.span_neg** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_neg (s : Set M) : span R (-s) = span R s
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_neg_eq_neg`：span_neg_eq_neg (s : Set M) : span R (-s) = -
span R s
· 使用定理 `Submodule.neg_eq_self`：neg_eq_self [Ring R] [AddCommGroup M] [Module R M
] (p : Submodule R M) : -p = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem span_neg (s : Set M) : span R (-s) = span R s := by simp [span_neg_eq_neg]
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsModularLattice (Submodule R M) := ⟨
  fun _ _ hxy _ _ => by rwa [← sup_inf_assoc_of_le_of_neg_le _ hxy (by simpa)]⟩
/-
**Submodule.isCompl_comap_subtype_of_isCompl_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Su
bmodule`。
形式化陈述：isCompl_comap_subtype_of_isCompl_of_le {p q r : Submodule R M} (h₁ : IsCom
pl q r) (h₂ : q <= p) : IsCompl (q.comap p.subtype) (r.comap p.subtype)
参数：h₁ : IsCompl q r；h₂ : q <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrderIso.isCompl_iff`：OrderIso.isCompl_iff {x y : α} : IsCompl x y ↔ IsC
ompl (f x) (f y)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_comap_subtype`：map_comap_subtype : map p.subtype (comap p.
subtype p') = p ⊓ p'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用引理 `Set.Iic.isCompl_inf_inf_of_isCompl_of_le`：Set.Iic.isCompl_inf_inf_of_isC
ompl_of_le [Lattice α] [BoundedOrder α] [IsModularLattice α] {a b c : α} (h₁ : I
sCompl b c) (h₂ : b <= a) : Is…
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
-/
lemma isCompl_comap_subtype_of_isCompl_of_le {p q r : Submodule R M}
    (h₁ : IsCompl q r) (h₂ : q ≤ p) :
    IsCompl (q.comap p.subtype) (r.comap p.subtype) := by
  simpa [p.mapIic.isCompl_iff, Iic.isCompl_iff] using Iic.isCompl_inf_inf_of_isCompl_of_le h₁ h₂

end AddCommGroup

section AddCommGroup

-- TODO: Multiple lemmas in this section should be in earlier files

variable [Semiring R] [Semiring R₂]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]

/-
**Submodule.comap_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule R M) : comap f (map f p) 
= p ⊔ LinearMap.ker f
参数：f : M ->ₛₗ[τ₁₂] M₂；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Submodule.le_comap_map`：le_comap_map [RingHomSurjective σ₁₂] (f : M ->ₛₗ
[σ₁₂] M₂) (p : Submodule R M) : p <= comap f (map f p)
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem comap_map_eq (f : M →ₛₗ[τ₁₂] M₂) (p : Submodule R M) :
    comap f (map f p) = p ⊔ LinearMap.ker f := by
  refine le_antisymm ?_ (sup_le (le_comap_map _ _) (comap_mono bot_le))
  rintro x ⟨y, hy, e⟩
  exact mem_sup.2 ⟨y, hy, x - y, by simpa using sub_eq_zero.2 e.symm, by simp⟩
/-
**Submodule.map_eq_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_eq_range_iff {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M} : map f p = f.ra
nge ↔ Codisjoint p f.ker
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_eq_range_iff {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M} :
    map f p = f.range ↔ Codisjoint p f.ker := by
  simp_rw [le_antisymm_iff, LinearMap.map_le_range, true_and, ← map_top, map_le_iff_le_comap,
    comap_map_eq, codisjoint_iff_le_sup]
/-
**Submodule.map_lt_map_of_le_of_sup_lt_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：map_lt_map_of_le_of_sup_lt_sup {p p' : Submodule R M} {f : M ->ₛₗ[τ₁₂] M₂}
 (hab : p <= p') (h : p ⊔ LinearMap.ker f < p' ⊔ LinearMap.ker f) : Submodule.ma
p f p < Submodule.map f p'
参数：hab : p <= p'；h : p ⊔ LinearMap.ker f < p' ⊔ LinearMap.ker f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Submodule.map_mono`：map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M}
 : p <= p' -> map f p <= map f p'
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem map_lt_map_of_le_of_sup_lt_sup {p p' : Submodule R M} {f : M →ₛₗ[τ₁₂] M₂} (hab : p ≤ p')
    (h : p ⊔ LinearMap.ker f < p' ⊔ LinearMap.ker f) : Submodule.map f p < Submodule.map f p' := by
  simp_rw [← comap_map_eq] at h
  exact lt_of_le_of_ne (map_mono hab) (ne_of_apply_ne _ h.ne)
/-
**Submodule.comap_map_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_map_eq_self {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M} (h : LinearMap.
ker f <= p) : comap f (map f p) = p
参数：h : LinearMap.ker f <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
-/
theorem comap_map_eq_self {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M} (h : LinearMap.ker f ≤ p) :
    comap f (map f p) = p := by rw [Submodule.comap_map_eq, sup_of_le_left h]
/-
**Submodule.comap_map_sup_of_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_map_sup_of_comap_le {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M} {q : Su
bmodule R₂ M₂} (le : comap f q <= p) : comap f (map f p ⊔ q) = p
参数：le : comap f q <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem comap_map_sup_of_comap_le {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
    (le : comap f q ≤ p) : comap f (map f p ⊔ q) = p := by
  refine le_antisymm (fun x h ↦ ?_) (map_le_iff_le_comap.mp le_sup_left)
  obtain ⟨_, ⟨y, hy, rfl⟩, z, hz, eq⟩ := mem_sup.mp h
  rw [add_comm, ← eq_sub_iff_add_eq, ← map_sub] at eq; subst eq
  simpa using p.add_mem (le hz) hy
/-
**Submodule.disjoint_map_of_ker_le_right** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：disjoint_map_of_ker_le_right {f : M ->ₛₗ[τ₁₂] M₂} {p q : Submodule R M} (h
pq : Disjoint p q) (hker : f.ker <= q) : Disjoint (p.map f) (q.map f)
参数：hpq : Disjoint p q；hker : f.ker <= q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Submodule.map_inf_eq_map_inf_comap`：map_inf_eq_map_inf_comap [RingHomSur
jective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {p' : Submodule R₂ M₂} : m
ap f p ⊓ p' = map f (p ⊓…
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Submodule.comap_bot`：comap_bot (f : M ->ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
lemma disjoint_map_of_ker_le_right {f : M →ₛₗ[τ₁₂] M₂} {p q : Submodule R M}
    (hpq : Disjoint p q) (hker : f.ker ≤ q) : Disjoint (p.map f) (q.map f) := by
  rw [disjoint_iff, map_inf_eq_map_inf_comap, comap_map_eq, eq_bot_iff, map_le_iff_le_comap,
    comap_bot, sup_eq_left.mpr hker, hpq.eq_bot]
  exact bot_le
/-
**Submodule.disjoint_map_of_ker_le_left** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：disjoint_map_of_ker_le_left {f : M ->ₛₗ[τ₁₂] M₂} {p q : Submodule R M} (hp
q : Disjoint p q) (hker : f.ker <= p) : Disjoint (p.map f) (q.map f)
参数：hpq : Disjoint p q；hker : f.ker <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用引理 `Submodule.disjoint_map_of_ker_le_right`：disjoint_map_of_ker_le_right {f 
: M ->ₛₗ[τ₁₂] M₂} {p q : Submodule R M} (hpq : Disjoint p q) (hker : f.ker <= q)
 : Disjoint (p.map f) (q.map…
-/
lemma disjoint_map_of_ker_le_left {f : M →ₛₗ[τ₁₂] M₂} {p q : Submodule R M}
    (hpq : Disjoint p q) (hker : f.ker ≤ p) : Disjoint (p.map f) (q.map f) :=
  disjoint_map_of_ker_le_right hpq.symm hker |>.symm
/-
**Submodule.isCoatom_comap_or_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isCoatom_comap_or_eq_top (f : M ->ₛₗ[τ₁₂] M₂) {p : Submodule R₂ M₂} (hp : 
IsCoatom p) : IsCoatom (comap f p) ∨ comap f p = ⊤
参数：f : M ->ₛₗ[τ₁₂] M₂；hp : IsCoatom p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.comap_map_sup_of_comap_le`：comap_map_sup_of_comap_le {f : M ->
ₛₗ[τ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂} (le : comap f q <= p) : co
map f (map f p ⊔ q) = p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Submodule.comap_top`：comap_top (f : M ->ₛₗ[σ₁₂] M₂) : comap f ⊤ = ⊤
-/
theorem isCoatom_comap_or_eq_top (f : M →ₛₗ[τ₁₂] M₂) {p : Submodule R₂ M₂} (hp : IsCoatom p) :
    IsCoatom (comap f p) ∨ comap f p = ⊤ :=
  or_iff_not_imp_right.mpr fun h ↦ ⟨h, fun q lt ↦ by
    rw [← comap_map_sup_of_comap_le lt.le, hp.2 (map f q ⊔ p), comap_top]
    simpa only [right_lt_sup, map_le_iff_le_comap] using lt.not_ge⟩
/-
**Submodule.isCoatom_comap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isCoatom_comap_iff {f : M ->ₛₗ[τ₁₂] M₂} (hf : Surjective f) {p : Submodule
 R₂ M₂} : IsCoatom (comap f p) ↔ IsCoatom p
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.comap_injective_of_surjective`：comap_injective_of_surjective :
 Function.Injective (comap f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCoatom.eq_1`：∀ {α : Type u_2} [inst : Preorder α] [inst_1 : OrderTop α
] (a : α), IsCoatom a = (a ≠ ⊤ ∧ ∀ (b : α), a < b → b = ⊤)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.comap_top`：comap_top (f : M ->ₛₗ[σ₁₂] M₂) : comap f ⊤ = ⊤
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Submodule.comap_strictMono_of_surjective`：comap_strictMono_of_surjective
 : StrictMono (comap f)
· 使用定理 `Submodule.lt_map_of_comap_lt_of_surjective`：lt_map_of_comap_lt_of_surjec
tive (h : q.comap f < p) : q < p.map f
· 使用定理 `Submodule.comap_map_eq_self`：comap_map_eq_self {f : M ->ₛₗ[τ₁₂] M₂} {p :
 Submodule R M} (h : LinearMap.ker f <= p) : comap f (map f p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem isCoatom_comap_iff {f : M →ₛₗ[τ₁₂] M₂} (hf : Surjective f) {p : Submodule R₂ M₂} :
    IsCoatom (comap f p) ↔ IsCoatom p := by
  have := comap_injective_of_surjective hf
  rw [IsCoatom, IsCoatom, ← comap_top f, this.ne_iff]
  refine and_congr_right fun _ ↦
    ⟨fun h m hm ↦ this (h _ <| comap_strictMono_of_surjective hf hm), fun h m hm ↦ ?_⟩
  rw [← h _ (lt_map_of_comap_lt_of_surjective hf hm),
    comap_map_eq_self ((comap_mono bot_le).trans hm.le)]
/-
**Submodule.isCoatom_map_of_ker_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isCoatom_map_of_ker_le {f : M ->ₛₗ[τ₁₂] M₂} (hf : Surjective f) {p : Submo
dule R M} (le : LinearMap.ker f <= p) (hp : IsCoatom p) : IsCoatom (map f p)
参数：hf : Surjective f；le : LinearMap.ker f <= p；hp : IsCoatom p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.isCoatom_comap_iff`：isCoatom_comap_iff {f : M ->ₛₗ[τ₁₂] M₂} (h
f : Surjective f) {p : Submodule R₂ M₂} : IsCoatom (comap f p) ↔ IsCoatom p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.comap_map_eq_self`：comap_map_eq_self {f : M ->ₛₗ[τ₁₂] M₂} {p :
 Submodule R M} (h : LinearMap.ker f <= p) : comap f (map f p) = p
-/
theorem isCoatom_map_of_ker_le {f : M →ₛₗ[τ₁₂] M₂} (hf : Surjective f) {p : Submodule R M}
    (le : LinearMap.ker f ≤ p) (hp : IsCoatom p) : IsCoatom (map f p) :=
  (isCoatom_comap_iff hf).mp <| by rwa [comap_map_eq_self le]
/-
**Submodule.map_iInf_of_ker_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_iInf_of_ker_le {f : M ->ₛₗ[τ₁₂] M₂} (hf : Surjective f) {ι} {p : ι -> 
Submodule R M} (h : LinearMap.ker f <= ⨅ i, p i) : map f (⨅ i, p i) = ⨅ i, map f
 (p i)
参数：hf : Surjective f；h : LinearMap.ker f <= ⨅ i, p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_comap_eq_of_surjective`：map_comap_eq_of_surjective (p : Su
bmodule R₂ M₂) : (p.comap f).map f = p
· 使用定理 `Submodule.comap_iInf`：comap_iInf {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι
 -> Submodule R₂ M₂) : comap f (⨅ i, p i) = ⨅ i, comap f (p i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.comap_map_eq_self`：comap_map_eq_self {f : M ->ₛₗ[τ₁₂] M₂} {p :
 Submodule R M} (h : LinearMap.ker f <= p) : comap f (map f p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iInf_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f : ι → α} {a : α}, a ≤ iInf f ↔ ∀ (i : ι), a ≤ f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_iInf_of_ker_le {f : M →ₛₗ[τ₁₂] M₂} (hf : Surjective f) {ι} {p : ι → Submodule R M}
    (h : LinearMap.ker f ≤ ⨅ i, p i) : map f (⨅ i, p i) = ⨅ i, map f (p i) := by
  conv_rhs => rw [← map_comap_eq_of_surjective hf (⨅ _, _), comap_iInf]
  simp_rw [fun i ↦ comap_map_eq_self (le_iInf_iff.mp h i)]
/-
**Submodule.comap_covBy_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：comap_covBy_of_surjective {f : M ->ₛₗ[τ₁₂] M₂} (hf : Surjective f) {p q : 
Submodule R₂ M₂} (h : p ⋖ q) : p.comap f ⋖ q.comap f
参数：hf : Surjective f；h : p ⋖ q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Submodule.comap_injective_of_surjective`：comap_injective_of_surjective :
 Function.Injective (comap f)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Submodule.lt_map_of_comap_lt_of_surjective`：lt_map_of_comap_lt_of_surjec
tive (h : q.comap f < p) : q < p.map f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.comap_lt_comap_iff_of_surjective`：comap_lt_comap_iff_of_surjec
tive {p q : Submodule R₂ M₂} : p.comap f < q.comap f ↔ p < q
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LinearMap.ker_le_comap`：ker_le_comap {p : Submodule R₂ M₂} (f : M ->ₛₗ[τ
₁₂] M₂) : ker f <= p.comap f
-/
lemma comap_covBy_of_surjective {f : M →ₛₗ[τ₁₂] M₂} (hf : Surjective f)
    {p q : Submodule R₂ M₂} (h : p ⋖ q) :
    p.comap f ⋖ q.comap f := by
  refine ⟨lt_of_le_of_ne (comap_mono h.1.le) ((comap_injective_of_surjective hf).ne h.1.ne), ?_⟩
  intro N h₁ h₂
  refine h.2 (lt_map_of_comap_lt_of_surjective hf h₁) ?_
  rwa [← comap_lt_comap_iff_of_surjective hf, comap_map_eq, sup_eq_left.mpr]
  refine (LinearMap.ker_le_comap (f : M →ₛₗ[τ₁₂] M₂)).trans h₁.le

@[deprecated map_eq_range_iff (since := "2026-07-01")]
/-
**Submodule._root_.LinearMap.range_domRestrict_eq_range_iff** 是 Mathlib 中的一个引理，位
于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearMap.range_domRestrict_eq_range_iff {f : M →ₛₗ[τ₁₂] M₂} {S : Submodule R M} :
    LinearMap.range (f.domRestrict S) = LinearMap.range f ↔ Codisjoint S f.ker := by
  simp [map_eq_range_iff]
/-
**Submodule._root_.LinearMap.surjective_domRestrict_iff** 是 Mathlib 中的一个引理，位于命名空
间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearMap.surjective_domRestrict_iff
    {f : M →ₛₗ[τ₁₂] M₂} {S : Submodule R M} (hf : Surjective f) :
    Surjective (f.domRestrict S) ↔ Codisjoint S f.ker := by
  rw [← LinearMap.range_eq_top] at hf ⊢
  rw [← hf, LinearMap.range_domRestrict, map_eq_range_iff]
/-
**Submodule.biSup_comap_eq_top_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Submodul
e`。
形式化陈述：biSup_comap_eq_top_of_surjective {ι : Type*} (s : Set ι) (hs : s.Nonempty)
 (p : ι -> Submodule R₂ M₂) (hp : ⨆ i in s, p i = ⊤) (f : M ->ₛₗ[τ₁₂] M₂) (hf : 
Surjective f) : ⨆ i in s, (p i).comap f = ⊤
参数：s : Set ι；hs : s.Nonempty；p : ι -> Submodule R₂ M₂；hp : ⨆ i in s, p i = ⊤；f :
 M ->ₛₗ[τ₁₂] M₂；hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
· 使用定理 `Submodule.map_iSup_comap_of_surjective`：map_iSup_comap_of_surjective {ι 
: Sort*} (S : ι -> Submodule R₂ M₂) : (⨆ i, (S i).comap f).map f = iSup S
· 使用定理 `Submodule.comap_top`：comap_top (f : M ->ₛₗ[σ₁₂] M₂) : comap f ⊤ = ⊤
· 使用定理 `left_eq_sup`：left_eq_sup : a = a ⊔ b ↔ b <= a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LinearMap.ker_le_comap`：ker_le_comap {p : Submodule R₂ M₂} (f : M ->ₛₗ[τ
₁₂] M₂) : ker f <= p.comap f
· 使用引理 `le_biSup`：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i 
in s) : f i <= ⨆ i in s, f i
-/
lemma biSup_comap_eq_top_of_surjective {ι : Type*} (s : Set ι) (hs : s.Nonempty)
    (p : ι → Submodule R₂ M₂) (hp : ⨆ i ∈ s, p i = ⊤)
    (f : M →ₛₗ[τ₁₂] M₂) (hf : Surjective f) :
    ⨆ i ∈ s, (p i).comap f = ⊤ := by
  obtain ⟨k, hk⟩ := hs
  suffices (⨆ i ∈ s, (p i).comap f) ⊔ LinearMap.ker f = ⊤ by
    rw [← this, left_eq_sup]; exact le_trans f.ker_le_comap (le_biSup (fun i ↦ (p i).comap f) hk)
  rw [iSup_subtype'] at hp ⊢
  rw [← comap_map_eq, map_iSup_comap_of_surjective hf, hp, comap_top]
/-
**Submodule.biSup_comap_eq_top_of_range_eq_biSup** 是 Mathlib 中的一个引理，位于命名空间 `Subm
odule`。
形式化陈述：biSup_comap_eq_top_of_range_eq_biSup {R R₂ : Type*} [Semiring R] [Ring R₂]
 {τ₁₂ : R ->+* R₂} [RingHomSurjective τ₁₂] [Module R M] [Module R₂ M₂] {ι : Type
*} (s : Set ι) (hs : s.Nonempty) (p : ι -> Submodule R₂ M₂) (f : M ->ₛₗ[τ₁₂] M₂)
 (hf : LinearMap.range f = ⨆ i in s, p i) : ⨆ i in s, (p i).comap f = ⊤
参数：s : Set ι；hs : s.Nonempty；p : ι -> Submodule R₂ M₂；f : M ->ₛₗ[τ₁₂] M₂；hf : Li
nearMap.range f = ⨆ i in s, p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.biSup_comap_subtype_eq_top`：biSup_comap_subtype_eq_top {ι : Ty
pe*} (s : Set ι) (p : ι -> Submodule R M) : ⨆ i in s, (p i).comap (⨆ i in s, p i
).subtype = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.biSup_comap_eq_top_of_surjective`：biSup_comap_eq_top_of_surjec
tive {ι : Type*} (s : Set ι) (hs : s.Nonempty) (p : ι -> Submodule R₂ M₂) (hp : 
⨆ i in s, p i = ⊤) (f : M ->ₛₗ[τ…
· 使用定理 `LinearMap.surjective_rangeRestrict`：surjective_rangeRestrict : Surjectiv
e f.rangeRestrict
-/
lemma biSup_comap_eq_top_of_range_eq_biSup
    {R R₂ : Type*} [Semiring R] [Ring R₂] {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]
    [Module R M] [Module R₂ M₂] {ι : Type*} (s : Set ι) (hs : s.Nonempty)
    (p : ι → Submodule R₂ M₂) (f : M →ₛₗ[τ₁₂] M₂) (hf : LinearMap.range f = ⨆ i ∈ s, p i) :
    ⨆ i ∈ s, (p i).comap f = ⊤ := by
  suffices ⨆ i ∈ s, (p i).comap (LinearMap.range f).subtype = ⊤ by
    rw [← biSup_comap_eq_top_of_surjective s hs _ this _ f.surjective_rangeRestrict]; rfl
  exact hf ▸ biSup_comap_subtype_eq_top s p

end AddCommGroup

section Ring

variable [Ring R] [Semiring R₂]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]
variable {p p' : Submodule R M}

/-
**Submodule.map_strict_mono_or_ker_sup_lt_ker_sup** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module`。
形式化陈述：map_strict_mono_or_ker_sup_lt_ker_sup (f : M ->ₛₗ[τ₁₂] M₂) (hab : p < p') 
: Submodule.map f p < Submodule.map f p' ∨ LinearMap.ker f ⊓ p < LinearMap.ker f
 ⊓ p'
参数：f : M ->ₛₗ[τ₁₂] M₂；hab : p < p'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.mk_lt_mk`：mk_lt_mk : (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ <= b₂ ∨ a₁ 
<= a₂ ∧ b₁ < b₂
· 使用定理 `strictMono_inf_prod_sup`：strictMono_inf_prod_sup : StrictMono fun x => (
x ⊓ z, x ⊔ z)
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Submodule.map_lt_map_of_le_of_sup_lt_sup`：map_lt_map_of_le_of_sup_lt_sup
 {p p' : Submodule R M} {f : M ->ₛₗ[τ₁₂] M₂} (hab : p <= p') (h : p ⊔ LinearMap.
ker f < p' ⊔ LinearMap.ker f) …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem map_strict_mono_or_ker_sup_lt_ker_sup (f : M →ₛₗ[τ₁₂] M₂) (hab : p < p') :
    Submodule.map f p < Submodule.map f p' ∨ LinearMap.ker f ⊓ p < LinearMap.ker f ⊓ p' := by
  obtain (⟨h, -⟩ | ⟨-, h⟩) := Prod.mk_lt_mk.mp <| strictMono_inf_prod_sup (z := LinearMap.ker f) hab
  · simpa [inf_comm] using Or.inr h
  · apply Or.inl <| map_lt_map_of_le_of_sup_lt_sup hab.le h
/-
**Submodule._root_.LinearMap.ker_inf_lt_ker_inf_of_map_eq_of_lt** 是 Mathlib 中的一个
定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.ker_inf_lt_ker_inf_of_map_eq_of_lt {f : M →ₛₗ[τ₁₂] M₂}
    (hab : p < p') (q : Submodule.map f p = Submodule.map f p') :
    LinearMap.ker f ⊓ p < LinearMap.ker f ⊓ p' :=
  map_strict_mono_or_ker_sup_lt_ker_sup f hab |>.resolve_left q.not_lt
/-
**Submodule.map_strict_mono_of_ker_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_strict_mono_of_ker_inf_eq {f : M ->ₛₗ[τ₁₂] M₂} (hab : p < p') (q : Lin
earMap.ker f ⊓ p = LinearMap.ker f ⊓ p') : Submodule.map f p < Submodule.map f p
'
参数：hab : p < p'；q : LinearMap.ker f ⊓ p = LinearMap.ker f ⊓ p'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Submodule.map_strict_mono_or_ker_sup_lt_ker_sup`：map_strict_mono_or_ker_
sup_lt_ker_sup (f : M ->ₛₗ[τ₁₂] M₂) (hab : p < p') : Submodule.map f p < Submodu
le.map f p' ∨ LinearMap.ker f ⊓ p < L…
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
-/
theorem map_strict_mono_of_ker_inf_eq {f : M →ₛₗ[τ₁₂] M₂} (hab : p < p')
    (q : LinearMap.ker f ⊓ p = LinearMap.ker f ⊓ p') : Submodule.map f p < Submodule.map f p' :=
  map_strict_mono_or_ker_sup_lt_ker_sup f hab |>.resolve_right q.not_lt

/-- Version of `disjoint_span_singleton` that works when the scalars are not a field. -/
/-
**Submodule.disjoint_span_singleton''** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：disjoint_span_singleton'' {s : Submodule R M} {x : M} : Disjoint s (R ∙ x)
 ↔ forall r : R, r • x in s -> r • x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Version of `disjoint_span_singleton` that works when the scalars are not a field
.
-/
lemma disjoint_span_singleton'' {s : Submodule R M} {x : M} :
    Disjoint s (R ∙ x) ↔ ∀ r : R, r • x ∈ s → r • x = 0 := by
  rw [disjoint_comm]; simp +contextual [disjoint_def, mem_span_singleton]

end Ring

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {s : Submodule K V} {x : V}

/-- There is no vector subspace between `s` and `K ∙ x ⊔ s`, `WCovBy` version. -/
/-
**Submodule.wcovBy_span_singleton_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：wcovBy_span_singleton_sup (x : V) (s : Submodule K V) : WCovBy s (K ∙ x ⊔ 
s)
参数：x : V；s : Submodule K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `SetLike.exists_of_lt`：exists_of_lt : p < q -> exists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
· 使用定理 `Submodule.add_mem_iff_left`：∀ {R : Type u} {M : Type v} [inst : Ring R] 
[inst_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {
x y : M}, y ∈ p …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
There is no vector subspace between `s` and `K ∙ x ⊔ s`, `WCovBy` version.
-/
theorem wcovBy_span_singleton_sup (x : V) (s : Submodule K V) : WCovBy s (K ∙ x ⊔ s) := by
  refine ⟨le_sup_right, fun q hpq hqp ↦ hqp.not_ge ?_⟩
  rcases SetLike.exists_of_lt hpq with ⟨y, hyq, hyp⟩
  obtain ⟨c, z, hz, rfl⟩ : ∃ c : K, ∃ z ∈ s, c • x + z = y := by
    simpa [mem_sup, mem_span_singleton] using hqp.le hyq
  rcases eq_or_ne c 0 with rfl | hc
  · simp [hz] at hyp
  · have : x ∈ q := by
      rwa [q.add_mem_iff_left (hpq.le hz), q.smul_mem_iff hc] at hyq
    simp [hpq.le, this]

/-- There is no vector subspace between `s` and `K ∙ x ⊔ s`, `CovBy` version. -/
/-
**Submodule.covBy_span_singleton_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：covBy_span_singleton_sup {x : V} {s : Submodule K V} (h : x ∉ s) : CovBy s
 (K ∙ x ⊔ s)
参数：h : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Submodule.wcovBy_span_singleton_sup`：wcovBy_span_singleton_sup (x : V) (
s : Submodule K V) : WCovBy s (K ∙ x ⊔ s)

--- 原说明 ---
There is no vector subspace between `s` and `K ∙ x ⊔ s`, `CovBy` version.
-/
theorem covBy_span_singleton_sup {x : V} {s : Submodule K V} (h : x ∉ s) : CovBy s (K ∙ x ⊔ s) :=
  ⟨by simpa, (wcovBy_span_singleton_sup _ _).2⟩
/-
**Submodule.disjoint_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：disjoint_span_singleton : Disjoint s (K ∙ x) ↔ x in s -> x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem disjoint_span_singleton : Disjoint s (K ∙ x) ↔ x ∈ s → x = 0 := by
  simpa +contextual [disjoint_span_singleton'', or_iff_not_imp_left, forall_comm (β := ¬_),
    s.smul_mem_iff] using ⟨fun h ↦ h _ one_ne_zero, fun h _ _ ↦ h⟩
/-
**Submodule.disjoint_span_singleton'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：disjoint_span_singleton' (hx : x != 0) : Disjoint s (K ∙ x) ↔ x ∉ s
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_span_singleton' (hx : x ≠ 0) : Disjoint s (K ∙ x) ↔ x ∉ s := by
  simp [disjoint_span_singleton, hx]
/-
**Submodule.disjoint_span_singleton_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Submodu
le`。
形式化陈述：disjoint_span_singleton_of_notMem (hx : x ∉ s) : Disjoint s (K ∙ x)
参数：hx : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
lemma disjoint_span_singleton_of_notMem (hx : x ∉ s) : Disjoint s (K ∙ x) := by
  simp [disjoint_span_singleton, hx]
/-
**Submodule.isCompl_span_singleton_of_isCoatom_of_notMem** 是 Mathlib 中的一个引理，位于命名
空间 `Submodule`。
形式化陈述：isCompl_span_singleton_of_isCoatom_of_notMem (hs : IsCoatom s) (hx : x ∉ s
) : IsCompl s (K ∙ x)
参数：hs : IsCoatom s；hx : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.disjoint_span_singleton_of_notMem`：disjoint_span_singleton_of_
notMem (hx : x ∉ s) : Disjoint s (K ∙ x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `covBy_top_iff`：covBy_top_iff : a ⋖ ⊤ ↔ IsCoatom a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Submodule.covBy_span_singleton_sup`：covBy_span_singleton_sup {x : V} {s 
: Submodule K V} (h : x ∉ s) : CovBy s (K ∙ x ⊔ s)
-/
lemma isCompl_span_singleton_of_isCoatom_of_notMem (hs : IsCoatom s) (hx : x ∉ s) :
    IsCompl s (K ∙ x) := by
  refine ⟨disjoint_span_singleton_of_notMem hx, ?_⟩
  rw [← covBy_top_iff] at hs
  simpa only [codisjoint_iff, sup_comm, not_lt_top_iff] using hs.2 (covBy_span_singleton_sup hx).1

end DivisionRing

end Submodule

namespace LinearMap

open Submodule Function

section AddCommGroup

variable [Semiring R] [Semiring R₂]
variable [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]

/-
**LinearMap.map_le_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_4} {M₂ : Type u_5} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommGroup M] [inst_3 : AddCommGr
oup M₂] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R₂ M₂]   {τ₁₂ : R →
+* R₂} [inst_6 : RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) {p p' : Submodule R 
M},   Submodule.map f p ≤ Submodule.map f p' ↔ p ≤ p' ⊔ f.ker
参数：f : M →ₛₗ[τ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem map_le_map_iff (f : M →ₛₗ[τ₁₂] M₂) {p p'} :
    map f p ≤ map f p' ↔ p ≤ p' ⊔ ker f := by
  rw [map_le_iff_le_comap, Submodule.comap_map_eq]
/-
**LinearMap.map_le_map_iff'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_le_map_iff' {f : M ->ₛₗ[τ₁₂] M₂} (hf : ker f = ⊥) {p p'} : map f p <= 
map f p' ↔ p <= p'
参数：hf : ker f = ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_le_map_iff`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_4
} {M₂ : Type u_5} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Group M] [inst…
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_le_map_iff' {f : M →ₛₗ[τ₁₂] M₂} (hf : ker f = ⊥) {p p'} :
    map f p ≤ map f p' ↔ p ≤ p' := by
  rw [LinearMap.map_le_map_iff, hf, sup_bot_eq]
/-
**LinearMap.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_injective {f : M ->ₛₗ[τ₁₂] M₂} (hf : ker f = ⊥) : Injective (map f)
参数：hf : ker f = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.map_le_map_iff'`：map_le_map_iff' {f : M ->ₛₗ[τ₁₂] M₂} (hf : ke
r f = ⊥) {p p'} : map f p <= map f p' ↔ p <= p'
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem map_injective {f : M →ₛₗ[τ₁₂] M₂} (hf : ker f = ⊥) : Injective (map f) := fun _ _ h =>
  le_antisymm ((map_le_map_iff' hf).1 (le_of_eq h)) ((map_le_map_iff' hf).1 (ge_of_eq h))
/-
**LinearMap.map_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_eq_top_iff {f : M ->ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) {p : Submodule R M}
 : p.map f = ⊤ ↔ p ⊔ LinearMap.ker f = ⊤
参数：hf : range f = ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_eq_top_iff {f : M →ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) {p : Submodule R M} :
    p.map f = ⊤ ↔ p ⊔ LinearMap.ker f = ⊤ := by
  simp_rw [← top_le_iff, ← hf, range_eq_map, LinearMap.map_le_map_iff]

end AddCommGroup

section

variable (R) (M) [Semiring R] [AddCommMonoid M] [Module R M]

/-- Given an element `x` of a module `M` over `R`, the natural map from
`R` to scalar multiples of `x`. See also `LinearMap.ringLmapEquivSelf`. -/
@[simps!]
/-
**LinearMap.toSpanSingleton** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toSpanSingleton (x : M) : R ->ₗ[R] M
参数：x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an element `x` of a module `M` over `R`, the natural map from
`R` to scalar multiples of `x`. See also `LinearMap.ringLmapEquivSelf`.
-/
def toSpanSingleton (x : M) : R →ₗ[R] M :=
  LinearMap.id.smulRight x
/-
**LinearMap.smulRight_id** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：smulRight_id : id.smulRight = toSpanSingleton R M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smulRight_id : id.smulRight = toSpanSingleton R M := rfl
/-
**LinearMap.toSpanSingleton_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toSpanSingleton_apply_one (x : M) : toSpanSingleton R M x 1 = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem toSpanSingleton_apply_one (x : M) : toSpanSingleton R M x 1 = x :=
  one_smul _ _
/-
**LinearMap.toSpanSingleton_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toSpanSingleton_injective : Function.Injective (toSpanSingleton R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem toSpanSingleton_injective : Function.Injective (toSpanSingleton R M) :=
  fun _ _ eq ↦ by simpa using congr($eq 1)

@[simp]
/-
**LinearMap.toSpanSingleton_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toSpanSingleton_zero : toSpanSingleton R M 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSpanSingleton_zero : toSpanSingleton R M 0 = 0 := by
  ext
  simp
/-
**LinearMap.toSpanSingleton_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toSpanSingleton_eq_zero_iff {x : M} : toSpanSingleton R M x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.toSpanSingleton_zero`：toSpanSingleton_zero : toSpanSingleton R
 M 0 = 0
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearMap.toSpanSingleton_injective`：toSpanSingleton_injective : Functio
n.Injective (toSpanSingleton R M)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSpanSingleton_eq_zero_iff {x : M} : toSpanSingleton R M x = 0 ↔ x = 0 := by
  rw [← toSpanSingleton_zero, (toSpanSingleton_injective R M).eq_iff]

variable {R M}
/-
**LinearMap.toSpanSingleton_add** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：toSpanSingleton_add (x y : M) : toSpanSingleton R M (x + y) = toSpanSingle
ton R M x + toSpanSingleton R M y
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSpanSingleton_add (x y : M) :
    toSpanSingleton R M (x + y) = toSpanSingleton R M x + toSpanSingleton R M y := by
  ext; simp
/-
**LinearMap.toSpanSingleton_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toSpanSingleton_smul {S : Type*} [Monoid S] [DistribMulAction S M] [SMulCo
mmClass R S M] (r : S) (x : M) : toSpanSingleton R M (r • x) = r • toSpanSinglet
on R M x
参数：r : S；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSpanSingleton_smul {S : Type*} [Monoid S] [DistribMulAction S M]
    [SMulCommClass R S M] (r : S) (x : M) :
    toSpanSingleton R M (r • x) = r • toSpanSingleton R M x := by
  ext; simp
/-
**LinearMap.toSpanSingleton_isIdempotentElem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
形式化陈述：toSpanSingleton_isIdempotentElem_iff {e : R} : IsIdempotentElem (toSpanSin
gleton R R e) ↔ IsIdempotentElem e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem toSpanSingleton_isIdempotentElem_iff {e : R} :
    IsIdempotentElem (toSpanSingleton R R e) ↔ IsIdempotentElem e := by
  simp_rw [IsIdempotentElem, LinearMap.ext_iff, Module.End.mul_apply, toSpanSingleton_apply,
    smul_eq_mul, mul_assoc]
  exact ⟨fun h ↦ by conv_rhs => rw [← one_mul e, ← h, one_mul], fun h _ ↦ by rw [h]⟩
/-
**LinearMap.isIdempotentElem_map_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isIdempotentElem_map_one_iff {f : Module.End R R} : IsIdempotentElem (f 1)
 ↔ IsIdempotentElem f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIdempotentElem.eq_1`：∀ {M : Type u_1} [inst : Mul M] (a : M), IsIdempo
tentElem a = (a * a = a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
theorem isIdempotentElem_map_one_iff {f : Module.End R R} :
    IsIdempotentElem (f 1) ↔ IsIdempotentElem f := by
  rw [IsIdempotentElem, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, IsIdempotentElem,
    LinearMap.ext_iff]
  simp_rw [Module.End.mul_apply]
  exact ⟨fun h r ↦ by rw [← mul_one r, ← smul_eq_mul, map_smul, map_smul, h], (· 1)⟩

/-- The range of `toSpanSingleton x` is the span of `x`. -/
/-
**LinearMap.range_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_toSpanSingleton (x : M) : range (toSpanSingleton R M x) = .span R {x
}
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_singleton_eq_range`：span_singleton_eq_range (y : M) : R ∙
 y = range ((· • y) : R -> M)

--- 原说明 ---
The range of `toSpanSingleton x` is the span of `x`.
-/
theorem range_toSpanSingleton (x : M) :
    range (toSpanSingleton R M x) = .span R {x} :=
  SetLike.coe_injective (Submodule.span_singleton_eq_range R x).symm

variable (R M) in
/-
**LinearMap.span_singleton_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：span_singleton_eq_range (x : M) : R ∙ x = range (toSpanSingleton R M x)
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_toSpanSingleton`：range_toSpanSingleton (x : M) : range (
toSpanSingleton R M x) = .span R {x}
-/
theorem span_singleton_eq_range (x : M) :
    R ∙ x = range (toSpanSingleton R M x) :=
  range_toSpanSingleton x |>.symm
/-
**LinearMap.comp_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_toSpanSingleton [AddCommMonoid M₂] [Module R M₂] (f : M ->ₗ[R] M₂) (x
 : M) : f ∘ₗ toSpanSingleton R M x = toSpanSingleton R M₂ (f x)
参数：f : M ->ₗ[R] M₂；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_toSpanSingleton [AddCommMonoid M₂] [Module R M₂] (f : M →ₗ[R] M₂) (x : M) :
    f ∘ₗ toSpanSingleton R M x = toSpanSingleton R M₂ (f x) := by
  ext; simp
/-
**LinearMap.submoduleOf_span_singleton_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap`。
形式化陈述：submoduleOf_span_singleton_of_mem (N : Submodule R M) {x : M} (hx : x in N
) : (span R {x}).submoduleOf N = span R {⟨x, hx⟩}
参数：N : Submodule R M；hx : x in N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem submoduleOf_span_singleton_of_mem (N : Submodule R M) {x : M} (hx : x ∈ N) :
    (span R {x}).submoduleOf N = span R {⟨x, hx⟩} := by
  ext y
  simp_rw [submoduleOf, mem_comap, subtype_apply, mem_span_singleton]
  aesop
/-
**LinearMap.ker_toSpanSingleton_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {x : R}, (LinearMap.toSpanSingleton R
 R x).ker = ⊥ ↔ x ∈ nonZeroDivisorsRight R
参数：LinearMap.toSpanSingleton R R x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
-/
@[simp] lemma ker_toSpanSingleton_eq_bot_iff {x : R} :
    ker (toSpanSingleton R R x) = ⊥ ↔ x ∈ nonZeroDivisorsRight R := le_bot_iff.symm

end

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [Semiring R₂] [AddCommMonoid M₂] [Module R₂ M₂]
variable {σ₁₂ : R →+* R₂}
include σ₁₂

/-- Two linear maps are equal on `Submodule.span s` iff they are equal on `s`. -/
/-
**LinearMap.eqOn_span_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eqOn_span_iff {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} : Set.EqOn f g (span R s)
 ↔ Set.EqOn f g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.le_eqLocus`：le_eqLocus {f g : M ->ₛₗ[τ₁₂] M₂} {S : Submodule R
 M} : S <= eqLocus f g ↔ Set.EqOn f g S
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two linear maps are equal on `Submodule.span s` iff they are equal on `s`.
-/
theorem eqOn_span_iff {s : Set M} {f g : M →ₛₗ[σ₁₂] M₂} :
    Set.EqOn f g (span R s) ↔ Set.EqOn f g s := by
  rw [← le_eqLocus, span_le]; rfl

/-- If two linear maps are equal on a set `s`, then they are equal on `Submodule.span s`.

This version uses `Set.EqOn`, and the hidden argument will expand to `h : x ∈ (span R s : Set M)`.
See `LinearMap.eqOn_span` for a version that takes `h : x ∈ span R s` as an argument. -/
/-
**LinearMap.eqOn_span'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eqOn_span' {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (H : Set.EqOn f g s) : Set.E
qOn f g (span R s : Set M)
参数：H : Set.EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.eqOn_span_iff`：eqOn_span_iff {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂
} : Set.EqOn f g (span R s) ↔ Set.EqOn f g s

--- 原说明 ---
If two linear maps are equal on a set `s`, then they are equal on `Submodule.spa
n s`.

This version uses `Set.EqOn`, and the hidden argument will expand to `h : x ∈ (s
pan R s : Set M)`.
See `LinearMap.eqOn_span` for a version that takes `h : x ∈ span R s` as an argu
ment.
-/
theorem eqOn_span' {s : Set M} {f g : M →ₛₗ[σ₁₂] M₂} (H : Set.EqOn f g s) :
    Set.EqOn f g (span R s : Set M) :=
  eqOn_span_iff.2 H

/-- If two linear maps are equal on a set `s`, then they are equal on `Submodule.span s`.

See also `LinearMap.eqOn_span'` for a version using `Set.EqOn`. -/
/-
**LinearMap.eqOn_span** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eqOn_span {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (H : Set.EqOn f g s) ⦃x⦄ (h :
 x in span R s) : f x = g x
参数：H : Set.EqOn f g s；h : x in span R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.eqOn_span'`：eqOn_span' {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (H :
 Set.EqOn f g s) : Set.EqOn f g (span R s : Set M)

--- 原说明 ---
If two linear maps are equal on a set `s`, then they are equal on `Submodule.spa
n s`.

See also `LinearMap.eqOn_span'` for a version using `Set.EqOn`.
-/
theorem eqOn_span {s : Set M} {f g : M →ₛₗ[σ₁₂] M₂} (H : Set.EqOn f g s) ⦃x⦄ (h : x ∈ span R s) :
    f x = g x :=
  eqOn_span' H h

/-- If `s` generates the whole module and linear maps `f`, `g` are equal on `s`, then they are
equal. -/
/-
**LinearMap.ext_on** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ext_on {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (hv : span R s = ⊤) (h : Set.EqO
n f g s) : f = g
参数：hv : span R s = ⊤；h : Set.EqOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `LinearMap.eqOn_span`：eqOn_span {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (H : S
et.EqOn f g s) ⦃x⦄ (h : x in span R s) : f x = g x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p

--- 原说明 ---
If `s` generates the whole module and linear maps `f`, `g` are equal on `s`, the
n they are
equal.
-/
theorem ext_on {s : Set M} {f g : M →ₛₗ[σ₁₂] M₂} (hv : span R s = ⊤) (h : Set.EqOn f g s) : f = g :=
  DFunLike.ext _ _ fun _ => eqOn_span h (eq_top_iff'.1 hv _)

/-- If the range of `v : ι → M` generates the whole module and linear maps `f`, `g` are equal at
each `v i`, then they are equal. -/
/-
**LinearMap.ext_on_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ext_on_range {ι : Sort*} {v : ι -> M} {f g : M ->ₛₗ[σ₁₂] M₂} (hv : span R 
(Set.range v) = ⊤) (h : forall i, f (v i) = g (v i)) : f = g
参数：hv : span R (Set.range v) = ⊤；h : forall i, f (v i) = g (v i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext_on`：ext_on {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (hv : span R
 s = ⊤) (h : Set.EqOn f g s) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)

--- 原说明 ---
If the range of `v : ι → M` generates the whole module and linear maps `f`, `g` 
are equal at
each `v i`, then they are equal.
-/
theorem ext_on_range {ι : Sort*} {v : ι → M} {f g : M →ₛₗ[σ₁₂] M₂} (hv : span R (Set.range v) = ⊤)
    (h : ∀ i, f (v i) = g (v i)) : f = g :=
  ext_on hv (Set.forall_mem_range.2 h)

end AddCommMonoid

section IsDomain

variable [Semiring R] [AddCommMonoid M] [Module R M] [IsDomain R] [Module.IsTorsionFree R M]

variable (R) in
/-
**LinearMap.ker_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_toSpanSingleton {x : M} (h : x != 0) : LinearMap.ker (toSpanSingleton 
R M x) = ⊥
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `or_iff_left_of_imp`：∀ {b a : Prop}, (b → a) → (a ∨ b ↔ a)
-/
theorem ker_toSpanSingleton {x : M} (h : x ≠ 0) : LinearMap.ker (toSpanSingleton R M x) = ⊥ :=
  SetLike.ext fun _ => smul_eq_zero.trans <| or_iff_left_of_imp fun h' => (h h').elim

end IsDomain

section Field

variable [Field K] [AddCommGroup V] [Module K V]

/-
**LinearMap.span_singleton_sup_ker_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：span_singleton_sup_ker_eq_top (f : V ->ₗ[K] K) {x : V} (hx : f x != 0) : K
 ∙ x ⊔ ker f = ⊤
参数：f : V ->ₗ[K] K；hx : f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `inv_mul_cancel_right₀`：inv_mul_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b⁻¹ * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem span_singleton_sup_ker_eq_top (f : V →ₗ[K] K) {x : V} (hx : f x ≠ 0) :
    K ∙ x ⊔ ker f = ⊤ :=
  top_unique fun y _ =>
    Submodule.mem_sup.2
      ⟨(f y * (f x)⁻¹) • x, Submodule.mem_span_singleton.2 ⟨f y * (f x)⁻¹, rfl⟩,
        ⟨y - (f y * (f x)⁻¹) • x, by simp [hx]⟩⟩

end Field

end LinearMap

open LinearMap

namespace LinearEquiv

variable (R M)
variable [Ring R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] (x : M)
  (h : x ≠ 0)

/-- Given a nonzero element `x` of a torsion-free module `M` over a ring `R`, the natural
isomorphism from `R` to the span of `x` given by $r \mapsto r \cdot x$. -/
noncomputable
/-
**LinearEquiv.toSpanNonzeroSingleton** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：toSpanNonzeroSingleton : R ≃ₗ[R] R ∙ x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toSpanNonzeroSingleton : R ≃ₗ[R] R ∙ x :=
  LinearEquiv.trans
    (LinearEquiv.ofInjective (LinearMap.toSpanSingleton R M x)
      (ker_eq_bot.1 <| ker_toSpanSingleton R h))
    (LinearEquiv.ofEq (range <| toSpanSingleton R M x) (R ∙ x) (range_toSpanSingleton x))
/-
**LinearEquiv.toSpanNonzeroSingleton_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEqui
v`。
形式化陈述：∀ (R : Type u_1) (M : Type u_4) [inst : Ring R] [inst_1 : IsDomain R] [ins
t_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [inst_4 : Module.IsTorsionF
ree R M] (x : M) (h : x ≠ 0) (t : R),   (LinearEquiv.toSpanNonzeroSingleton R M 
x h) t = ⟨t • x, ⋯⟩
参数：R : Type u_1；M : Type u_4；x : M；h : x ≠ 0；t : R；LinearEquiv.toSpanNonzeroSing
leton R M x h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toSpanNonzeroSingleton_apply (t : R) :
    toSpanNonzeroSingleton R M x h t =
      (⟨t • x, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)⟩ : R ∙ x) := by
  rfl

@[simp]
/-
**LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul** 是 Mathlib 中的一个引理，位于命名空间 `
LinearEquiv`。
形式化陈述：toSpanNonzeroSingleton_symm_apply_smul (m : R ∙ x) : (toSpanNonzeroSinglet
on R M x h).symm m • x = m
参数：m : R ∙ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
lemma toSpanNonzeroSingleton_symm_apply_smul (m : R ∙ x) :
    (toSpanNonzeroSingleton R M x h).symm m • x = m :=
  congrArg Subtype.val <| apply_symm_apply (toSpanNonzeroSingleton R M x h) m
/-
**LinearEquiv.toSpanNonzeroSingleton_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`
。
形式化陈述：toSpanNonzeroSingleton_one : LinearEquiv.toSpanNonzeroSingleton R M x h 1 
= (⟨x, Submodule.mem_span_singleton_self x⟩ : R ∙ x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.toSpanNonzeroSingleton_apply`：∀ (R : Type u_1) (M : Type u_4
) [inst : Ring R] [inst_1 : IsDomain R] [inst_2 : AddCommGroup M]   [inst_3 : _r
oot_.Module R M] [inst_4 : Mod…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSpanNonzeroSingleton_one :
    LinearEquiv.toSpanNonzeroSingleton R M x h 1 =
      (⟨x, Submodule.mem_span_singleton_self x⟩ : R ∙ x) := by simp

/-- Given a nonzero element `x` of a torsion-free module `M` over a ring `R`, the natural
isomorphism from the span of `x` to `R` given by $r \cdot x \mapsto r$. -/
noncomputable
/-
**LinearEquiv.coord** 是 Mathlib 中的一个缩写定义，位于命名空间 `LinearEquiv`。
形式化陈述：coord : R ∙ x ≃ₗ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev coord : R ∙ x ≃ₗ[R] R :=
  (toSpanNonzeroSingleton R M x h).symm
/-
**LinearEquiv.coord_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coord_self : (coord R M x h) (⟨x, Submodule.mem_span_singleton_self x⟩ : R
 ∙ x) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.toSpanNonzeroSingleton_one`：toSpanNonzeroSingleton_one : Lin
earEquiv.toSpanNonzeroSingleton R M x h 1 = (⟨x, Submodule.mem_span_singleton_se
lf x⟩ : R ∙ x)
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem coord_self : (coord R M x h) (⟨x, Submodule.mem_span_singleton_self x⟩ : R ∙ x) = 1 := by
  rw [← toSpanNonzeroSingleton_one R M x h, LinearEquiv.symm_apply_apply]
/-
**LinearEquiv.coord_apply_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coord_apply_smul (y : Submodule.span R ({x} : Set M)) : coord R M x h y • 
x = y
参数：y : Submodule.span R ({x} : Set M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem coord_apply_smul (y : Submodule.span R ({x} : Set M)) : coord R M x h y • x = y :=
  Subtype.ext_iff.1 <| (toSpanNonzeroSingleton R M x h).apply_symm_apply _

end LinearEquiv

