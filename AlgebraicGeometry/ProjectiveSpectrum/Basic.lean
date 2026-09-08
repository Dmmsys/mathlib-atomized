/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Gluing

/-!

# Basic properties of the scheme `Proj A`

The scheme `Proj 𝒜` for a graded ring `𝒜` is constructed in
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean`.
In this file we provide basic properties of the scheme.

## Main results
- `AlgebraicGeometry.Proj.toSpecZero`: The structure map `Proj A ⟶ Spec (A 0)`.
- `AlgebraicGeometry.Proj.basicOpenIsoSpec`:
  The canonical isomorphism `Proj A |_ D₊(f) ≅ Spec (A_f)₀`
  when `f` is homogeneous of positive degree.
- `AlgebraicGeometry.Proj.awayι`: The open immersion `Spec (A_f)₀ ⟶ Proj A`.
- `AlgebraicGeometry.Proj.affineOpenCover`: The open cover of `Proj A` by `Spec (A_f)₀` for all
  homogeneous `f` of positive degree.
- `AlgebraicGeometry.Proj.stalkIso`:
  The stalk of `Proj A` at `x` is the degree `0` part of the localization of `A` at `x`.
- `AlgebraicGeometry.Proj.fromOfGlobalSections`:
  Given a map `f : A →+* Γ(X, ⊤)` such that the image of the irrelevant ideal under `f`
  generates the whole ring, we can construct a map `X ⟶ Proj 𝒜`.

-/

@[expose] public section

namespace AlgebraicGeometry.Proj

open HomogeneousLocalization CategoryTheory

universe u

variable {σ : Type*} {A : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ)
variable [GradedRing 𝒜]

section basicOpen

variable (f g : A)

/-- The basic open set `D₊(f)` associated to `f : A`. -/
/-
**AlgebraicGeometry.Proj.basicOpen** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.
Proj`。
形式化陈述：basicOpen : (Proj 𝒜).Opens
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basic open set `D₊(f)` associated to `f : A`.
-/
def basicOpen : (Proj 𝒜).Opens :=
  ProjectiveSpectrum.basicOpen 𝒜 f

@[simp]
/-
**AlgebraicGeometry.Proj.mem_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Proj`。
形式化陈述：mem_basicOpen (x : Proj 𝒜) : x in basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal
参数：x : Proj 𝒜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_basicOpen (x : Proj 𝒜) :
    x ∈ basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal :=
  Iff.rfl
/-
**AlgebraicGeometry.Proj.basicOpen_one** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Proj`。
形式化陈述：∀ {σ : Type u_1} {A : Type u} [inst : CommRing A] [inst_1 : SetLike σ A] [
inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRing 𝒜], AlgebraicG
eometry.Proj.basicOpen 𝒜 1 = ⊤
参数：𝒜 : ℕ → σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.basicOpen_one`：basicOpen_one : basicOpen 𝒜 (1 : A) = 
⊤
-/
@[simp] theorem basicOpen_one : basicOpen 𝒜 1 = ⊤ := ProjectiveSpectrum.basicOpen_one ..
/-
**AlgebraicGeometry.Proj.basicOpen_zero** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.Proj`。
形式化陈述：∀ {σ : Type u_1} {A : Type u} [inst : CommRing A] [inst_1 : SetLike σ A] [
inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRing 𝒜], AlgebraicG
eometry.Proj.basicOpen 𝒜 0 = ⊥
参数：𝒜 : ℕ → σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.basicOpen_zero`：basicOpen_zero : basicOpen 𝒜 (0 : A) 
= ⊥
-/
@[simp] theorem basicOpen_zero : basicOpen 𝒜 0 = ⊥ := ProjectiveSpectrum.basicOpen_zero ..
/-
**AlgebraicGeometry.Proj.basicOpen_pow** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Proj`。
形式化陈述：∀ {σ : Type u_1} {A : Type u} [inst : CommRing A] [inst_1 : SetLike σ A] [
inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRing 𝒜] (f : A) (n 
: ℕ),   0 < n → AlgebraicGeometry.Proj.basicOpen 𝒜 (f ^ n) = AlgebraicGeometry.P
roj.basicOpen 𝒜 f
参数：𝒜 : ℕ → σ；f : A；n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.basicOpen_pow`：basicOpen_pow (f : A) (n : Nat) (hn : 
0 < n) : basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f
-/
@[simp] theorem basicOpen_pow (n) (hn : 0 < n) : basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f :=
  ProjectiveSpectrum.basicOpen_pow 𝒜 f n hn
/-
**AlgebraicGeometry.Proj.basicOpen_mul** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Proj`。
形式化陈述：basicOpen_mul : basicOpen 𝒜 (f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.basicOpen_mul`：basicOpen_mul (f g : A) : basicOpen 𝒜 
(f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g
-/
theorem basicOpen_mul : basicOpen 𝒜 (f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g :=
  ProjectiveSpectrum.basicOpen_mul ..
/-
**AlgebraicGeometry.Proj.basicOpen_mono** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.Proj`。
形式化陈述：basicOpen_mono (hfg : f ∣ g) : basicOpen 𝒜 g <= basicOpen 𝒜 f
参数：hfg : f ∣ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `AlgebraicGeometry.Proj.basicOpen_mul`：basicOpen_mul : basicOpen 𝒜 (f * g
) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem basicOpen_mono (hfg : f ∣ g) : basicOpen 𝒜 g ≤ basicOpen 𝒜 f :=
  (hfg.choose_spec ▸ basicOpen_mul 𝒜 f _).trans_le inf_le_left
/-
**AlgebraicGeometry.Proj.basicOpen_eq_iSup_proj** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Proj`。
形式化陈述：basicOpen_eq_iSup_proj (f : A) : basicOpen 𝒜 f = ⨆ i : Nat, basicOpen 𝒜 (G
radedRing.proj 𝒜 i f)
参数：f : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.basicOpen_eq_union_of_projection`：basicOpen_eq_union_
of_projection (f : A) : basicOpen 𝒜 f = ⨆ i : Nat, basicOpen 𝒜 (GradedRing.proj 
𝒜 i f)
-/
theorem basicOpen_eq_iSup_proj (f : A) :
    basicOpen 𝒜 f = ⨆ i : ℕ, basicOpen 𝒜 (GradedRing.proj 𝒜 i f) :=
  ProjectiveSpectrum.basicOpen_eq_union_of_projection ..
/-
**AlgebraicGeometry.Proj.isBasis_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Proj`。
形式化陈述：isBasis_basicOpen : TopologicalSpace.Opens.IsBasis (Set.range (basicOpen 𝒜
))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `ProjectiveSpectrum.isTopologicalBasis_basic_opens`：isTopologicalBasis_ba
sic_opens : TopologicalSpace.IsTopologicalBasis (Set.range fun r : A => (basicOp
en 𝒜 r : Set (ProjectiveSpectrum 𝒜)))
-/
theorem isBasis_basicOpen :
    TopologicalSpace.Opens.IsBasis (Set.range (basicOpen 𝒜)) := by
  delta TopologicalSpace.Opens.IsBasis
  convert! ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜
  exact (Set.range_comp _ _).symm

/-- If `{ xᵢ }` spans the irrelevant ideal of `A`, then `D₊(xᵢ)` covers `Proj A`. -/
/-
**AlgebraicGeometry.Proj.iSup_basicOpen_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.Proj`。
形式化陈述：iSup_basicOpen_eq_top {ι : Type*} (f : ι -> A) (hf : (HomogeneousIdeal.irr
elevant 𝒜).toIdeal <= Ideal.span (Set.range f)) : ⨆ i, Proj.basicOpen 𝒜 (f i) = 
⊤
参数：f : ι -> A；hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal <= Ideal.span (Set.ra
nge f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.Opens.mem_iSup`：mem_iSup {ι} {x : α} {s : ι -> Opens α}
 : x in iSup s ↔ exists i, x in s i
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `ProjectiveSpectrum.not_irrelevant_le`：∀ {A : Type u_1} {σ : Type u_2} [i
nst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubmonoidClass σ A] {𝒜 : ℕ
 → σ}   [inst_3 : GradedRi…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
If `{ xᵢ }` spans the irrelevant ideal of `A`, then `D₊(xᵢ)` covers `Proj A`.
-/
lemma iSup_basicOpen_eq_top {ι : Type*} (f : ι → A)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range f)) :
    ⨆ i, Proj.basicOpen 𝒜 (f i) = ⊤ := by
  classical
  refine top_le_iff.mp fun x hx ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
  by_contra! H
  simp only [mem_basicOpen, Decidable.not_not] at H
  refine x.not_irrelevant_le (hf.trans ?_)
  rwa [Ideal.span_le, Set.range_subset_iff]

/-- If `{ xᵢ }` are homogeneous and span `A` as an `A₀` algebra, then `D₊(xᵢ)` covers `Proj A`. -/
/-
**AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Proj`。
形式化陈述：iSup_basicOpen_eq_top' {ι : Type*} (f : ι -> A) (hfn : forall i, exists n,
 f i in 𝒜 n) (hf : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) : ⨆ i, Proj.basicOpen
 𝒜 (f i) = ⊤
参数：f : ι -> A；hfn : forall i, exists n, f i in 𝒜 n；hf : Algebra.adjoin (𝒜 0) (Se
t.range f) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用引理 `AlgebraicGeometry.Proj.iSup_basicOpen_eq_top`：iSup_basicOpen_eq_top {ι :
 Type*} (f : ι -> A) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal <= Ideal.span
 (Set.range f)) : ⨆ i, Proj.basicO…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GradedRing.projZeroRingHom_apply`：∀ {ι : Type u_1} {A : Type u_3} {σ : T
ype u_4} [inst : Semiring A] [inst_1 : DecidableEq ι] [inst_2 : AddCommMonoid ι]
   [inst_3 : PartialOr…
· 使用定理 `GradedRing.proj_apply`：GradedRing.proj_apply (i : ι) (r : A) : GradedRin
g.proj 𝒜 i r = (decompose 𝒜 r : ⨁ i, 𝒜 i) i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `HomogeneousIdeal.mem_irrelevant_iff`：mem_irrelevant_iff (a : A) : a in 𝒜
₊ ↔ proj 𝒜 0 a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_iff_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
· 使用定理 `trivial`：True
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `DirectSum.decompose_of_mem_same`：decompose_of_mem_same {x : M} {i : ι} (
hx : x in ℳ i) : (decompose ℳ x i : M) = x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `DirectSum.decompose_of_mem_ne`：decompose_of_mem_ne {x : M} {i j : ι} (hx
 : x in ℳ i) (hij : i != j) : (decompose ℳ x j : M) = 0
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
（共 65 条，此处仅展示前 30 条）

--- 原说明 ---
If `{ xᵢ }` are homogeneous and span `A` as an `A₀` algebra, then `D₊(xᵢ)` cover
s `Proj A`.
-/
lemma iSup_basicOpen_eq_top' {ι : Type*} (f : ι → A)
    (hfn : ∀ i, ∃ n, f i ∈ 𝒜 n)
    (hf : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) :
    ⨆ i, Proj.basicOpen 𝒜 (f i) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  intro x hx
  convert_to x - GradedRing.projZeroRingHom 𝒜 x ∈ _
  · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
      (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
  clear hx
  have := (eq_iff_iff.mp congr(x ∈ $hf)).mpr trivial
  induction this using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hfn i
    rw [GradedRing.projZeroRingHom_apply]
    by_cases hn' : n = 0
    · rw [DirectSum.decompose_of_mem_same 𝒜 (hn' ▸ hn), sub_self]
      exact zero_mem _
    · rw [DirectSum.decompose_of_mem_ne 𝒜 hn hn', sub_zero]
      exact Ideal.subset_span ⟨_, rfl⟩
  | algebraMap r =>
    convert! zero_mem (Ideal.span _)
    rw [sub_eq_zero]
    exact (DirectSum.decompose_of_mem_same 𝒜 r.2).symm
  | add x y hx hy _ _ =>
    rw [map_add, add_sub_add_comm]
    exact add_mem ‹_› ‹_›
  | mul x y hx hy hx' hy' =>
    convert!
      add_mem (Ideal.mul_mem_left _ x hy')
        (Ideal.mul_mem_right (GradedRing.projZeroRingHom 𝒜 y) _ hx') using 1
    rw [map_mul]
    ring

/-- The canonical map `(A_f)₀ ⟶ Γ(Proj A, D₊(f))`.
This is an isomorphism when `f` is homogeneous of positive degree. See `basicOpenIsoAway` below. -/
/-
**AlgebraicGeometry.Proj.awayToSection** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Proj`。
形式化陈述：awayToSection : CommRingCat.of (Away 𝒜 f) ⟶ Γ(Proj 𝒜, basicOpen 𝒜 f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `(A_f)₀ ⟶ Γ(Proj A, D₊(f))`.
This is an isomorphism when `f` is homogeneous of positive degree. See `basicOpe
nIsoAway` below.
-/
def awayToSection : CommRingCat.of (Away 𝒜 f) ⟶ Γ(Proj 𝒜, basicOpen 𝒜 f) :=
  ProjectiveSpectrum.Proj.awayToSection ..

/-- The canonical map `Proj A |_ D₊(f) ⟶ Spec (A_f)₀`.
This is an isomorphism when `f` is homogeneous of positive degree. See `basicOpenIsoSpec` below. -/
noncomputable
/-
**AlgebraicGeometry.Proj.basicOpenToSpec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Proj`。
形式化陈述：basicOpenToSpec : (basicOpen 𝒜 f).toScheme ⟶ Spec (.of <| Away 𝒜 f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def basicOpenToSpec : (basicOpen 𝒜 f).toScheme ⟶ Spec (.of <| Away 𝒜 f) :=
  (basicOpen 𝒜 f).toSpecΓ ≫ Spec.map (awayToSection 𝒜 f)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Proj.basicOpenToSpec_app_top** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Proj`。
形式化陈述：basicOpenToSpec_app_top : (basicOpenToSpec 𝒜 f).app ⊤ = (Scheme.ΓSpecIso _
).hom ≫ awayToSection 𝒜 f ≫ (basicOpen 𝒜 f).topIso.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Opens.toSpecΓ_appTop`：∀ {X : AlgebraicGeometry.
Scheme} (U : X.Opens),   AlgebraicGeometry.Scheme.Hom.appTop U.toSpecΓ =     Cat
egoryTheory.CategoryStruct.comp (Al…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.topIso_inv`：∀ {X : AlgebraicGeometry.Sche
me} (U : X.Opens), U.topIso.inv = X.presheaf.map (CategoryTheory.eqToHom ⋯).op
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `AlgebraicGeometry.Scheme.ΓSpecIso_naturality_assoc`：∀ {R S : CommRingCat
} (f : R ⟶ S) {Z : CommRingCat} (h : S ⟶ Z),   CategoryTheory.CategoryStruct.com
p (AlgebraicGeometry.Scheme.Hom.appTop (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma basicOpenToSpec_app_top :
    (basicOpenToSpec 𝒜 f).app ⊤ = (Scheme.ΓSpecIso _).hom ≫ awayToSection 𝒜 f ≫
      (basicOpen 𝒜 f).topIso.inv := by
  simp [basicOpenToSpec, Scheme.Opens.toSpecΓ_appTop]

/-- The structure map `Proj A ⟶ Spec A₀`. -/
noncomputable
/-
**AlgebraicGeometry.Proj.toSpecZero** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry
.Proj`。
形式化陈述：toSpecZero : Proj 𝒜 ⟶ Spec (.of <| 𝒜 0)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Proj.basicOpen_one`：∀ {σ : Type u_1} {A : Type u} [ins
t : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ → 
σ)   [inst_3 : GradedRing …
-/
def toSpecZero : Proj 𝒜 ⟶ Spec (.of <| 𝒜 0) :=
  (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ (basicOpen_one _)).inv ≫
    basicOpenToSpec 𝒜 1 ≫ Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _))

variable {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)

/-- The canonical isomorphism `Proj A |_ D₊(f) ≅ Spec (A_f)₀`
when `f` is homogeneous of positive degree. -/
@[simps! -isSimp hom]
noncomputable
/-
**AlgebraicGeometry.Proj.basicOpenIsoSpec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Proj`。
形式化陈述：basicOpenIsoSpec : (basicOpen 𝒜 f).toScheme ≅ Spec (.of <| Away 𝒜 f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def basicOpenIsoSpec : (basicOpen 𝒜 f).toScheme ≅ Spec (.of <| Away 𝒜 f) :=
  have : IsIso (basicOpenToSpec 𝒜 f) := by
    apply (isIso_iff_of_reflects_iso _ Scheme.forgetToLocallyRingedSpace).mp ?_
    convert! ProjectiveSpectrum.Proj.isIso_toSpec 𝒜 f f_deg hm using 1
    refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
    dsimp [basicOpenToSpec, Scheme.Opens.toSpecΓ]
    simp only [Category.assoc, ← Spec.map_comp]
    rfl
  asIso (basicOpenToSpec 𝒜 f)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism `(A_f)₀ ≅ Γ(Proj A, D₊(f))`
when `f` is homogeneous of positive degree. -/
@[simps! -isSimp hom]
noncomputable
/-
**AlgebraicGeometry.Proj.basicOpenIsoAway** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Proj`。
形式化陈述：basicOpenIsoAway : CommRingCat.of (Away 𝒜 f) ≅ Γ(Proj 𝒜, basicOpen 𝒜 f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def basicOpenIsoAway : CommRingCat.of (Away 𝒜 f) ≅ Γ(Proj 𝒜, basicOpen 𝒜 f) :=
  have : IsIso (awayToSection 𝒜 f) := by
    have := basicOpenToSpec_app_top 𝒜 f
    rw [← Iso.inv_comp_eq, Iso.eq_comp_inv] at this
    rw [← this, ← basicOpenIsoSpec_hom 𝒜 f f_deg hm]
    infer_instance
  asIso (awayToSection 𝒜 f)

/-- The open immersion `Spec (A_f)₀ ⟶ Proj A`. -/
noncomputable
/-
**AlgebraicGeometry.Proj.away** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Proj`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def awayι : Spec (.of <| Away 𝒜 f) ⟶ Proj 𝒜 :=
  (basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι

@[reassoc]
/-
**AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.Proj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma basicOpenIsoSpec_inv_ι :
    (basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι = awayι 𝒜 f f_deg hm := rfl
/-
**AlgebraicGeometry.Proj.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Proj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOpenImmersion (Proj.awayι 𝒜 f f_deg hm) :=
  IsOpenImmersion.comp _ _
/-
**AlgebraicGeometry.Proj.opensRange_away** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.Proj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opensRange_awayι :
    (Proj.awayι 𝒜 f f_deg hm).opensRange = Proj.basicOpen 𝒜 f :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (basicOpen 𝒜 f).opensRange_ι

include f_deg hm in
/-
**AlgebraicGeometry.Proj.isAffineOpen_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Proj`。
形式化陈述：isAffineOpen_basicOpen : IsAffineOpen (basicOpen 𝒜 f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AlgebraicGeometry.Proj.instIsOpenImmersionAwayι`：∀ {σ : Type u_1} {A : T
ype u} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass σ A
] (𝒜 : ℕ → σ)   [inst_3 : GradedRing …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Proj.opensRange_awayι`：opensRange_awayι : (Proj.awayι 
𝒜 f f_deg hm).opensRange = Proj.basicOpen 𝒜 f
· 使用定理 `AlgebraicGeometry.isAffineOpen_opensRange`：isAffineOpen_opensRange {X Y 
: Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen f.open
sRange
-/
lemma isAffineOpen_basicOpen : IsAffineOpen (basicOpen 𝒜 f) := by
  rw [← opensRange_awayι 𝒜 f f_deg hm]
  exact isAffineOpen_opensRange (awayι _ _ _ _)

@[reassoc]
/-
**AlgebraicGeometry.Proj.away** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Proj`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma awayι_toSpecZero : awayι 𝒜 f f_deg hm ≫ toSpecZero 𝒜 =
    Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _)) := by
  rw [toSpecZero, basicOpenToSpec, awayι]
  simp only [Category.assoc, Iso.inv_comp_eq, basicOpenIsoSpec_hom]
  have (U) (e : U = ⊤) : (basicOpen 𝒜 f).ι ≫ (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ e).inv =
      Scheme.homOfLE _ (le_top.trans_eq e.symm) := by
    simp only [← Category.assoc, Iso.comp_inv_eq]
    simp only [Scheme.topIso_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.homOfLE_ι]
  rw [reassoc_of% this, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, basicOpenToSpec,
    Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  rfl

variable {f}
variable {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m') (hm' : 0 < m') {x : A} (hx : x = f * g)

@[reassoc]
/-
**AlgebraicGeometry.Proj.awayMap_awayToSection** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.Proj`。
形式化陈述：awayMap_awayToSection : CommRingCat.ofHom (awayMap 𝒜 g_deg hx) ≫ awayToSec
tion 𝒜 x = awayToSection 𝒜 f ≫ (Proj 𝒜).presheaf.map (homOfLE (basicOpen_mono _ 
_ _ ⟨_, hx⟩)).op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `AlgebraicGeometry.Proj.basicOpen_mono`：basicOpen_mono (hfg : f ∣ g) : ba
sicOpen 𝒜 g <= basicOpen 𝒜 f
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用引理 `HomogeneousLocalization.mk_surjective`：mk_surjective : Function.Surjecti
ve (mk (𝒜
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `Submonoid.powers_le`：powers_le {n : M} {P : Submonoid M} : powers n <= P
 ↔ n in P
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection_apply`：awayToSec
tion_apply (f : A) (x p) : (((ProjectiveSpectrum.Proj.awayToSection 𝒜 f).1 x).va
l p).val = IsLocalization.map (M
· 使用引理 `CommRingCat.hom_ofHom`：hom_ofHom {R S : Type u} [CommRing R] [CommRing S
] (f : R ->+* S) : (ofHom f).hom = f
· 使用定理 `Submonoid.mem_powers_iff`：mem_powers_iff (x z : M) : x in powers z ↔ exi
sts n : Nat, z ^ n = x
· 使用引理 `HomogeneousLocalization.val_awayMap_mk`：val_awayMap_mk (n a i hi) : (awa
yMap 𝒜 hg hx (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, rfl⟩⟩)).val = Localization.mk (a * g ^ 
i) ⟨x ^ i, (Submonoid.mem_po…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `IsLocalization.map_mk'`：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = m
k' Q (g x) ⟨g y, hy y.2⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `Localization.mk_eq_mk_iff`：mk_eq_mk_iff {a c : M} {b d : S} : mk a b = m
k c d ↔ r S ⟨a, b⟩ ⟨c, d⟩
· 使用定理 `Localization.r_iff_exists`：r_iff_exists {x y : M × S} : r S x y ↔ exists
 c : S, ↑c * (↑y.2 * x.1) = c * (x.2 * y.1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 49 条，此处仅展示前 30 条）
-/
lemma awayMap_awayToSection :
    CommRingCat.ofHom (awayMap 𝒜 g_deg hx) ≫ awayToSection 𝒜 x =
      awayToSection 𝒜 f ≫ (Proj 𝒜).presheaf.map (homOfLE (basicOpen_mono _ _ _ ⟨_, hx⟩)).op := by
  ext a
  apply Subtype.ext
  ext ⟨i, hi⟩
  obtain ⟨⟨n, a, ⟨b, hb'⟩, i, rfl : _ = b⟩, rfl⟩ := mk_surjective a
  simp only [homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [CommRingCat.hom_ofHom, val_awayMap_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    ← Localization.mk_eq_mk']
  refine Localization.mk_eq_mk_iff.mpr ?_
  rw [Localization.r_iff_exists]
  use 1
  simp [hx]
  ring

@[reassoc]
/-
**AlgebraicGeometry.Proj.basicOpenToSpec_SpecMap_awayMap** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.Proj`。
形式化陈述：basicOpenToSpec_SpecMap_awayMap : basicOpenToSpec 𝒜 x ≫ Spec.map (CommRing
Cat.ofHom (awayMap 𝒜 g_deg hx)) = (Proj 𝒜).homOfLE (basicOpen_mono _ _ _ ⟨_, hx⟩
) ≫ basicOpenToSpec 𝒜 f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AlgebraicGeometry.Proj.basicOpen_mono`：basicOpen_mono (hfg : f ∣ g) : ba
sicOpen 𝒜 g <= basicOpen 𝒜 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Proj.basicOpenToSpec.eq_1`：∀ {σ : Type u_1} {A : Type 
u} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass σ A] (𝒜
 : ℕ → σ)   [inst_3 : GradedRing …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用引理 `AlgebraicGeometry.Proj.awayMap_awayToSection`：awayMap_awayToSection : Co
mmRingCat.ofHom (awayMap 𝒜 g_deg hx) ≫ awayToSection 𝒜 x = awayToSection 𝒜 f ≫ (
Proj 𝒜).presheaf.map (homOfLE (bas…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc`：∀ {X 
: AlgebraicGeometry.Scheme} (U V : X.Opens) (h : U ≤ V) {Z : AlgebraicGeometry.S
cheme}   (h_1 : AlgebraicGeometry.Spec (X.presheaf.obj …
-/
lemma basicOpenToSpec_SpecMap_awayMap :
    basicOpenToSpec 𝒜 x ≫ Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) =
      (Proj 𝒜).homOfLE (basicOpen_mono _ _ _ ⟨_, hx⟩) ≫ basicOpenToSpec 𝒜 f := by
  rw [basicOpenToSpec, Category.assoc, ← Spec.map_comp, awayMap_awayToSection,
    Spec.map_comp, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
  rfl

@[reassoc]
/-
**AlgebraicGeometry.Proj.SpecMap_awayMap_away** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Proj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma SpecMap_awayMap_awayι :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) ≫ awayι 𝒜 f f_deg hm =
      awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m')) := by
  rw [awayι, awayι, Iso.eq_inv_comp, basicOpenIsoSpec_hom, basicOpenToSpec_SpecMap_awayMap_assoc,
  ← basicOpenIsoSpec_hom _ _ f_deg hm, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]

/-- The isomorphism `D₊(f) ×[Proj 𝒜] D₊(g) ≅ D₊(fg)`. -/
noncomputable
/-
**AlgebraicGeometry.Proj.pullbackAway** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.Proj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pullbackAwayιIso :
    Limits.pullback (awayι 𝒜 f f_deg hm) (awayι 𝒜 g g_deg hm') ≅ Spec (.of <| Away 𝒜 x) :=
    IsOpenImmersion.isoOfRangeEq (Limits.pullback.fst _ _ ≫ awayι 𝒜 f f_deg hm)
      (awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m'))) <| by
  rw [IsOpenImmersion.range_pullback_to_base_of_left]
  change ((awayι 𝒜 f _ _).opensRange ⊓ (awayι 𝒜 g _ _).opensRange).1 = (awayι 𝒜 _ _ _).opensRange.1
  rw [opensRange_awayι, opensRange_awayι, opensRange_awayι, ← basicOpen_mul, hx]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Proj.pullbackAway** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry.Proj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullbackAwayιIso_hom_awayι :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m')) =
      Limits.pullback.fst _ _ ≫ awayι 𝒜 f f_deg hm :=
  IsOpenImmersion.isoOfRangeEq_hom_fac ..

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Proj.pullbackAway** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry.Proj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullbackAwayιIso_hom_SpecMap_awayMap_left :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) = Limits.pullback.fst _ _ := by
  rw [← cancel_mono (awayι 𝒜 f f_deg hm), ← pullbackAwayιIso_hom_awayι,
    Category.assoc, SpecMap_awayMap_awayι]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Proj.pullbackAway** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry.Proj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullbackAwayιIso_hom_SpecMap_awayMap_right :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 f_deg (hx.trans (mul_comm _ _)))) =
      Limits.pullback.snd _ _ := by
  rw [← cancel_mono (awayι 𝒜 g g_deg hm'), ← Limits.pullback.condition,
    ← pullbackAwayιIso_hom_awayι 𝒜 f_deg hm g_deg hm' hx,
    Category.assoc, SpecMap_awayMap_awayι]
  rfl

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Proj.pullbackAway** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry.Proj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullbackAwayιIso_inv_fst :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).inv ≫ Limits.pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) := by
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_left, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Proj.pullbackAway** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry.Proj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullbackAwayιIso_inv_snd :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).inv ≫ Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 f_deg (hx.trans (mul_comm _ _)))) := by
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_right (hx := hx) .., Iso.inv_hom_id_assoc]

include hm' in
/-
**AlgebraicGeometry.Proj.away** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Proj`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma awayι_preimage_basicOpen :
    awayι 𝒜 f f_deg hm ⁻¹ᵁ basicOpen 𝒜 g =
      PrimeSpectrum.basicOpen (Away.isLocalizationElem f_deg g_deg) := by
  ext1
  trans Set.range (Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg rfl)))
  · rw [← pullbackAwayιIso_inv_fst 𝒜 f_deg hm g_deg hm' rfl]
    simp only [TopologicalSpace.Opens.map_coe, Scheme.Hom.comp_base,
      TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp]
    rw [Set.range_eq_univ.mpr (by exact
      (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' rfl).inv.homeomorph.surjective),
      ← opensRange_awayι _ _ g_deg hm']
    simp [IsOpenImmersion.range_pullbackFst]
  · let := (awayMap (f := f) 𝒜 g_deg rfl).toAlgebra
    let := HomogeneousLocalization.Away.isLocalization_mul f_deg g_deg rfl hm.ne'
    exact PrimeSpectrum.localization_away_comap_range _ _

open TopologicalSpace.Opens in
/-- Given a family of homogeneous elements `f` of positive degree that spans the irrelevant ideal,
`Spec (A_f)₀ ⟶ Proj A` forms an affine open cover of `Proj A`. -/
noncomputable
/-
**AlgebraicGeometry.Proj.affineOpenCoverOfIrrelevantLESpan** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicGeometry.Proj`。
形式化陈述：affineOpenCoverOfIrrelevantLESpan {ι : Type*} (f : ι -> A) {m : ι -> Nat} 
(f_deg : forall i, f i in 𝒜 (m i)) (hm : forall i, 0 < m i) (hf : (HomogeneousId
eal.irrelevant 𝒜).toIdeal <= Ideal.span (Set.range f)) : (Proj 𝒜).AffineOpenCove
r where I₀
参数：f : ι -> A；f_deg : forall i, f i in 𝒜 (m i)；hm : forall i, 0 < m i；hf : (Homo
geneousIdeal.irrelevant 𝒜).toIdeal <= Ideal.span (Set.range f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def affineOpenCoverOfIrrelevantLESpan {ι : Type*} (f : ι → A) {m : ι → ℕ}
    (f_deg : ∀ i, f i ∈ 𝒜 (m i)) (hm : ∀ i, 0 < m i)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range f)) :
    (Proj 𝒜).AffineOpenCover where
  I₀ := ι
  X i := .of (Away 𝒜 (f i))
  f i := awayι 𝒜 (f i) (f_deg i) (hm i)
  idx x := (mem_iSup.mp ((iSup_basicOpen_eq_top 𝒜 f hf).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (awayι 𝒜 _ _ _).opensRange
    rw [opensRange_awayι]
    exact (mem_iSup.mp ((iSup_basicOpen_eq_top 𝒜 f hf).ge (Set.mem_univ x))).choose_spec

/-- `Proj A` is covered by `Spec (A_f)₀` for all homogeneous elements of positive degree. -/
@[simps! f] noncomputable
/-
**AlgebraicGeometry.Proj.affineOpenCover** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Proj`。
形式化陈述：affineOpenCover : (Proj 𝒜).AffineOpenCover
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Proj A` is covered by `Spec (A_f)₀` for all homogeneous elements of positive de
gree.
-/
def affineOpenCover : (Proj 𝒜).AffineOpenCover :=
  affineOpenCoverOfIrrelevantLESpan 𝒜
    (ι := Σ i : PNat, 𝒜 i) (m := fun i ↦ i.1) (fun i ↦ i.2) (fun i ↦ i.2.2) (fun i ↦ i.1.2) <| by
  classical
  intro z hz
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  refine Ideal.sum_mem _ fun c hc ↦ if hc0 : c = 0 then ?_ else
    Ideal.subset_span ⟨⟨⟨c, Nat.pos_iff_ne_zero.mpr hc0⟩, _⟩, rfl⟩
  convert! Ideal.zero_mem _
  subst hc0
  exact hz

end basicOpen

section stalk

set_option backward.isDefEq.respectTransparency.types false in
/-- The stalk of `Proj A` at `x` is the degree `0` part of the localization of `A` at `x`. -/
noncomputable
/-
**AlgebraicGeometry.Proj.stalkIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.P
roj`。
形式化陈述：stalkIso (x : Proj 𝒜) : (Proj 𝒜).presheaf.stalk x ≅ .of (AtPrime 𝒜 x.asHom
ogeneousIdeal.toIdeal)
参数：x : Proj 𝒜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def stalkIso (x : Proj 𝒜) :
    (Proj 𝒜).presheaf.stalk x ≅ .of (AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
  (stalkIso' 𝒜 x).toCommRingCatIso

end stalk

noncomputable section ofGlobalSection

open Limits

variable {X : Scheme.{u}} (f : A →+* Γ(X, ⊤)) {x x' : Γ(X, ⊤)} {t t' : A} {d d' : ℕ}

/-- Given a graded ring `A` and a map `f : A →+* Γ(X, ⊤)`,
for each homogeneous `t` of positive degree, it induces a map from `D(f(t)) ⟶ D₊(t)`. -/
/-
**AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Proj`。
形式化陈述：toBasicOpenOfGlobalSections (H : f t = x) (h0d : 0 < d) (hd : t in 𝒜 d) : 
(X.basicOpen x).toScheme ⟶ basicOpen 𝒜 t
参数：H : f t = x；h0d : 0 < d；hd : t in 𝒜 d。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_preimage_basicOpen`：∀ (X : AlgebraicGeo
metry.Scheme) (r : ↑(X.presheaf.obj (Opposite.op ⊤))),   (TopologicalSpace.Opens
.map X.toSpecΓ.base).obj (PrimeSpectrum.b…

--- 原说明 ---
Given a graded ring `A` and a map `f : A →+* Γ(X, ⊤)`,
for each homogeneous `t` of positive degree, it induces a map from `D(f(t)) ⟶ D₊
(t)`.
-/
def toBasicOpenOfGlobalSections (H : f t = x) (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    (X.basicOpen x).toScheme ⟶ basicOpen 𝒜 t := by
  refine ?_ ≫ (basicOpenIsoSpec _ _ hd h0d).inv
  refine (X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫ X.toSpecΓ ∣_ _ ≫ ?_
  refine (basicOpenIsoSpecAway _).hom ≫
    Spec.map (CommRingCat.ofHom (RingHom.comp ?_ (algebraMap _ (Localization.Away t))))
  refine IsLocalization.map (M := .powers t) (T := .powers x) _ f ?_
  · rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]
    simp [H]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**AlgebraicGeometry.Proj.homOfLE_toBasicOpenOfGlobalSections_** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.Proj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homOfLE_toBasicOpenOfGlobalSections_ι
    {H : f t = x} {h0d : 0 < d} {hd : t ∈ 𝒜 d} {H' : f t' = x'} {h0d' : 0 < d'} {hd' : t' ∈ 𝒜 d'}
    {s : A} (hts : t * s = t') {n : ℕ} (hn : d + n = d') (hs : s ∈ 𝒜 n) :
    X.homOfLE (by aesop) ≫ toBasicOpenOfGlobalSections 𝒜 f H h0d hd ≫ (basicOpen 𝒜 t).ι =
      toBasicOpenOfGlobalSections 𝒜 f H' h0d' hd' ≫ (basicOpen 𝒜 t').ι := by
  simp only [toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv,
    ← Scheme.Hom.resLE_eq_morphismRestrict, CommRingCat.ofHom_comp, Spec.map_comp,
    Scheme.Hom.map_resLE_assoc, Category.assoc, basicOpenIsoSpec_inv_ι]
  have hx'x : PrimeSpectrum.basicOpen x' ≤ PrimeSpectrum.basicOpen x := by
    aesop (add simp PrimeSpectrum.basicOpen_mul)
  rw [← Scheme.Hom.resLE_map_assoc _ (by simp [X.toSpecΓ_preimage_basicOpen]) hx'x]
  congr 1
  simp only [← Iso.inv_comp_eq]
  subst hts hn
  rw [← SpecMap_awayMap_awayι (𝒜 := 𝒜) hd h0d
    hs rfl, basicOpenIsoSpecAway_inv_homOfLE_assoc (R := Γ(X, ⊤)) x (f s) x' (by simp [← H', H]),
    Iso.inv_hom_id_assoc]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext
  simp only [RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_awayMap]
  simp only [← RingHom.comp_apply]
  congr 1
  apply IsLocalization.ringHom_ext (M := .powers t)
  ext i
  simp [IsLocalization.Away.awayToAwayRight_eq]

variable (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)

set_option backward.isDefEq.respectTransparency false in
/-- Given a graded ring `A` and a map `f : A →+* Γ(X, ⊤)` such that the image of the
irrelevant ideal under `f` generates the whole ring, the set of `D(f(r))` for homogeneous `r`
of positive degree forms an open cover on `X`. -/
/-
**AlgebraicGeometry.Proj.openCoverOfMapIrrelevantEqTop** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.Proj`。
形式化陈述：openCoverOfMapIrrelevantEqTop : X.OpenCover
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a graded ring `A` and a map `f : A →+* Γ(X, ⊤)` such that the image of the
irrelevant ideal under `f` generates the whole ring, the set of `D(f(r))` for ho
mogeneous `r`
of positive degree forms an open cover on `X`.
-/
def openCoverOfMapIrrelevantEqTop : X.OpenCover :=
  X.openCoverOfIsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦
    X.basicOpen (f ir.2.1)) (by
    classical
    have H : Ideal.span (Set.range fun x : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦ x.2.1) =
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
      apply le_antisymm
      · rw [Ideal.span_le, Set.range_subset_iff]
        rintro ⟨i, r, hi0, hri⟩
        simp [-ZeroMemClass.coe_eq_zero,
          DirectSum.decompose_of_mem_ne 𝒜 hri hi0.ne']
      · intro x hx
        rw [← DirectSum.sum_support_decompose 𝒜 x]
        refine Ideal.sum_mem _ fun c hc ↦ ?_
        have : c ≠ 0 := by contrapose hc; simpa [hc] using hx
        exact Ideal.subset_span ⟨⟨c, _, this.bot_lt, by simp⟩, rfl⟩
    ext1
    apply compl_injective
    simp only [TopologicalSpace.Opens.coe_iSup, Set.compl_iUnion, ← Scheme.zeroLocus_singleton,
      ← Scheme.zeroLocus_iUnion, Set.iUnion_singleton_eq_range, TopologicalSpace.Opens.coe_top,
      Set.compl_univ]
    rw [← Scheme.zeroLocus_span, Set.range_comp', ← Ideal.map_span, H, hf]
    simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given a graded ring `A` and a map `f : A →+* Γ(X, ⊤)` such that the image of the
irrelevant ideal under `f` generates the whole ring, we can construct a map `X ⟶ Proj 𝒜`. -/
/-
**AlgebraicGeometry.Proj.fromOfGlobalSections** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Proj`。
形式化陈述：fromOfGlobalSections : X ⟶ Proj 𝒜
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a graded ring `A` and a map `f : A →+* Γ(X, ⊤)` such that the image of the
irrelevant ideal under `f` generates the whole ring, we can construct a map `X ⟶
 Proj 𝒜`.
-/
def fromOfGlobalSections : X ⟶ Proj 𝒜 := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 f hf).glueMorphisms
    (fun ri ↦ toBasicOpenOfGlobalSections 𝒜 f rfl ri.2.2.1 ri.2.2.2 ≫ Scheme.Opens.ι _) ?_
  rintro x y
  let e : pullback ((openCoverOfMapIrrelevantEqTop 𝒜 f hf).f x)
      ((openCoverOfMapIrrelevantEqTop 𝒜 f hf).f y) ≅ (X.basicOpen (f (x.snd.fst * y.snd.fst))) :=
    (isPullback_opens_inf _ _).isoPullback.symm ≪≫ X.isoOfEq (by simp)
  rw [← cancel_epi e.inv]
  trans toBasicOpenOfGlobalSections 𝒜 f rfl (Nat.add_pos_left x.2.2.1 y.1)
    (SetLike.mul_mem_graded x.2.2.2 y.2.2.2) ≫ (Scheme.Opens.ι _)
  · simpa [e, openCoverOfMapIrrelevantEqTop, Scheme.isoOfEq_inv] using
      homOfLE_toBasicOpenOfGlobalSections_ι _ _ rfl rfl y.2.2.2
  · simpa [e, openCoverOfMapIrrelevantEqTop, Scheme.isoOfEq_inv] using
      (homOfLE_toBasicOpenOfGlobalSections_ι _ _ (mul_comm _ _) (add_comm _ _) x.2.2.2).symm

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Proj`。
形式化陈述：fromOfGlobalSections_preimage_basicOpen {r : A} {n : Nat} (hn : 0 < n) (hr
 : r in 𝒜 n) : fromOfGlobalSections 𝒜 f hf ⁻¹ᵁ basicOpen 𝒜 r = X.basicOpen (f r)
参数：hn : 0 < n；hr : r in 𝒜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AlgebraicGeometry.Scheme.Cover.exists_eq`：∀ {K : CategoryTheory.Precover
age AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [AlgebraicGeometr
y.Scheme.JointlySurjective K] …
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_preimage_basicOpen`：∀ (X : AlgebraicGeo
metry.Scheme) (r : ↑(X.presheaf.obj (Opposite.op ⊤))),   (TopologicalSpace.Opens
.map X.toSpecΓ.base).obj (PrimeSpectrum.b…
· 使用定理 `TopologicalSpace.Opens.map_coe`：map_coe (f : X ⟶ Y) (U : Opens Y) : ((ma
p f).obj U : Set X) = f ⁻¹' (U : Set Y)
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `IsLocalization.map_mk'`：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = m
k' Q (g x) ⟨g y, hy y.2⟩
· 使用定理 `IsLocalization.mk'.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M : Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Ideal.pow_mem_of_mem`：pow_mem_of_mem (ha : a in I) (n : Nat) (hn : 0 < n
) : a ^ n in I
· 使用定理 `Ideal.le_radical`：le_radical : I <= radical I
· 使用定理 `Ideal.mem_span_singleton_self`：mem_span_singleton_self (x : α) : x in sp
an ({x} : Set α)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
（共 48 条，此处仅展示前 30 条）
-/
lemma fromOfGlobalSections_preimage_basicOpen {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    fromOfGlobalSections 𝒜 f hf ⁻¹ᵁ basicOpen 𝒜 r = X.basicOpen (f r) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i, x, rfl⟩ := (openCoverOfMapIrrelevantEqTop 𝒜 f hf).exists_eq x
    rw [← SetLike.mem_coe] at hx -- TODO : mem version of TopologicalSpace.Opens.map_coe
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      ← Scheme.Hom.comp_apply, fromOfGlobalSections, Scheme.Cover.ι_glueMorphisms] at hx
    simp only [openCoverOfMapIrrelevantEqTop,
      toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv, Category.assoc, basicOpenIsoSpec_inv_ι] at hx
    simp only [Scheme.Hom.comp_base, Scheme.homOfLE_base, homOfLE_leOfHom, TopCat.hom_comp,
      ContinuousMap.comp_assoc, ContinuousMap.comp_apply, morphismRestrict_base,
      TopologicalSpace.Opens.carrier_eq_coe] at hx
    rw [← SetLike.mem_coe, ← Set.mem_preimage, ← TopologicalSpace.Opens.map_coe,
      Proj.awayι_preimage_basicOpen (𝒜 := 𝒜) i.2.2.2 i.2.2.1 hr hn,
      ← Set.mem_preimage, ← TopologicalSpace.Opens.map_coe, ← Function.Injective.mem_set_image
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) _))).isOpenEmbedding.injective,
      ← Scheme.Hom.comp_apply, basicOpenIsoSpecAway, IsOpenImmersion.isoOfRangeEq_hom_fac] at hx
    rw [← SetLike.mem_coe, ← Scheme.toSpecΓ_preimage_basicOpen, TopologicalSpace.Opens.map_coe,
        Set.mem_preimage]
    refine Set.mem_of_subset_of_mem (Set.image_subset_iff.mpr ?_) hx
    change PrimeSpectrum.basicOpen _ ≤ PrimeSpectrum.basicOpen _
    simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk', map_pow,
      PrimeSpectrum.basicOpen_le_basicOpen_iff, IsLocalization.mk'_mem_iff]
    exact Ideal.pow_mem_of_mem _ (Ideal.le_radical (Ideal.mem_span_singleton_self _)) _ i.2.2.1
  · intro x hx
    let I : (openCoverOfMapIrrelevantEqTop 𝒜 f hf).I₀ := ⟨n, r, hn, hr⟩
    obtain ⟨x, rfl⟩ : x ∈ ((openCoverOfMapIrrelevantEqTop 𝒜 f hf).f I).opensRange := by
      simpa [openCoverOfMapIrrelevantEqTop] using hx
    rw [← SetLike.mem_coe] -- TODO : mem version of TopologicalSpace.Opens.map_coe
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage,
      ← Scheme.Hom.comp_apply, fromOfGlobalSections]
    simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Proj.fromOfGlobalSections_morphismRestrict** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.Proj`。
形式化陈述：fromOfGlobalSections_morphismRestrict {r : A} {n : Nat} (hn : 0 < n) (hr :
 r in 𝒜 n) : (fromOfGlobalSections 𝒜 f hf) ∣_ (basicOpen 𝒜 r) = (Scheme.isoOfEq 
_ (fromOfGlobalSections_preimage_basicOpen _ _ _ hn hr)).hom ≫ toBasicOpenOfGlob
alSections 𝒜 f rfl hn hr
参数：hn : 0 < n；hr : r in 𝒜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用引理 `AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen`：fromOfGl
obalSections_preimage_basicOpen {r : A} {n : Nat} (hn : 0 < n) (hr : r in 𝒜 n) :
 fromOfGlobalSections 𝒜 f hf ⁻¹ᵁ basicOpen 𝒜 r = X.b…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι_assoc`：∀ (X : AlgebraicGeometry.Schem
e) {U V : X.Opens} (e : U ≤ V) {Z : AlgebraicGeometry.Scheme} (h : X ⟶ Z),   Cat
egoryTheory.CategoryStruct.com…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms`：ι_glueMorphisms (𝒰 : Ope
nCover.{v} X) {Y : Scheme} (f : forall x, 𝒰.X x ⟶ Y) (hf : forall x y, pullback.
fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback…
-/
lemma fromOfGlobalSections_morphismRestrict {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    (fromOfGlobalSections 𝒜 f hf) ∣_ (basicOpen 𝒜 r) =
      (Scheme.isoOfEq _ (fromOfGlobalSections_preimage_basicOpen _ _ _ hn hr)).hom ≫
        toBasicOpenOfGlobalSections 𝒜 f rfl hn hr := by
  rw [← Iso.inv_comp_eq, ← cancel_mono (basicOpen 𝒜 r).ι]
  simp only [Scheme.isoOfEq_inv, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
    fromOfGlobalSections]
  exact (openCoverOfMapIrrelevantEqTop 𝒜 f hf).ι_glueMorphisms _ _ ⟨_, _, hn, hr⟩
/-
**AlgebraicGeometry.Proj.fromOfGlobalSections_resLE** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.Proj`。
形式化陈述：fromOfGlobalSections_resLE {r : A} {n : Nat} (hn : 0 < n) (hr : r in 𝒜 n) 
: (fromOfGlobalSections 𝒜 f hf).resLE _ _ (fromOfGlobalSections_preimage_basicOp
en _ _ _ hn hr).ge = toBasicOpenOfGlobalSections 𝒜 f rfl hn hr
参数：hn : 0 < n；hr : r in 𝒜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen`：fromOfGl
obalSections_preimage_basicOpen {r : A} {n : Nat} (hn : 0 < n) (hr : r in 𝒜 n) :
 fromOfGlobalSections 𝒜 f hf ⁻¹ᵁ basicOpen 𝒜 r = X.b…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用引理 `AlgebraicGeometry.Proj.fromOfGlobalSections_morphismRestrict`：fromOfGlob
alSections_morphismRestrict {r : A} {n : Nat} (hn : 0 < n) (hr : r in 𝒜 n) : (fr
omOfGlobalSections 𝒜 f hf) ∣_ (basicOpen 𝒜 r) = (S…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict`：resLE_eq_morphis
mRestrict : f.resLE U (f ⁻¹ᵁ U) le_rfl = f ∣_ U
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.map_resLE`：map_resLE (i : V' <= V) : X.homO
fLE i ≫ f.resLE U V e = f.resLE U V' (i.trans e)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromOfGlobalSections_resLE {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    (fromOfGlobalSections 𝒜 f hf).resLE _ _
      (fromOfGlobalSections_preimage_basicOpen _ _ _ hn hr).ge =
      toBasicOpenOfGlobalSections 𝒜 f rfl hn hr := by
  rw [← (Iso.inv_comp_eq _).mpr (fromOfGlobalSections_morphismRestrict 𝒜 f hf hn hr),
    ← Scheme.Hom.resLE_eq_morphismRestrict]
  simp [Scheme.isoOfEq_inv]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.Proj.fromOfGlobalSections_toSpecZero** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.Proj`。
形式化陈述：fromOfGlobalSections_toSpecZero (f : A ->+* Γ(X, ⊤)) (hf : (HomogeneousIde
al.irrelevant 𝒜).toIdeal.map f = ⊤) : fromOfGlobalSections 𝒜 f hf ≫ toSpecZero 𝒜
 = X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (f.comp (algebraMap _ _)))
参数：f : A ->+* Γ(X, ⊤)；hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.hom_ext`：hom_ext (𝒰 : OpenCover.{v} X) {Y
 : Scheme} (f₁ f₂ : X ⟶ Y) (h : forall x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_preimage_basicOpen`：∀ (X : AlgebraicGeo
metry.Scheme) (r : ↑(X.presheaf.obj (Opposite.op ⊤))),   (TopologicalSpace.Opens
.map X.toSpecΓ.base).obj (PrimeSpectrum.b…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.glueMorphisms.congr_simp`：∀ {X : Algebrai
cGeometry.Scheme} (𝒰 : X.OpenCover) {Y : AlgebraicGeometry.Scheme} (f f_1 : (x :
 𝒰.I₀) → 𝒰.X x ⟶ Y)   (e_f : f = f_1)   (hf :…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms_assoc`：∀ {X : AlgebraicGe
ometry.Scheme} (𝒰 : X.OpenCover) {Y : AlgebraicGeometry.Scheme} (f : (x : 𝒰.I₀) 
→ 𝒰.X x ⟶ Y)   (hf :     ∀ (x y : 𝒰.I₀),  …
· 使用定理 `AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι_assoc`：∀ {σ : Type u_1} {A
 : Type u} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass
 σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRing …
· 使用引理 `AlgebraicGeometry.Proj.awayι_toSpecZero`：awayι_toSpecZero : awayι 𝒜 f f_
deg hm ≫ toSpecZero 𝒜 = Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _))
· 使用定理 `AlgebraicGeometry.Scheme.openCoverOfIsOpenCover_f`：∀ {s : Type u_1} (X :
 AlgebraicGeometry.Scheme) (U : s → X.Opens) (hU : TopologicalSpace.IsOpenCover 
U) (i : s),   (X.openCoverOfIsOpenCover…
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_hom_ι_assoc`：∀ (X : AlgebraicGeometry.S
cheme) {U V : X.Opens} (e : U = V) {Z : AlgebraicGeometry.Scheme} (h : X ⟶ Z),  
 CategoryTheory.CategoryStruct.com…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_inv_fac_assoc`：∀ {X Y Z :
 AlgebraicGeometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [inst : AlgebraicGeometry.IsO
penImmersion f]   [inst_1 : AlgebraicGeometry.IsOp…
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `HomogeneousLocalization.instIsScalarTowerSubtypeMemOfNatLocalization`：∀ 
{ι : Type u_1} {A : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLi
ke σ A]   [inst_2 : AddSubgroupClass σ A] [inst_3 : AddCom…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
-/
lemma fromOfGlobalSections_toSpecZero
    (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    fromOfGlobalSections 𝒜 f hf ≫ toSpecZero 𝒜 =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (f.comp (algebraMap _ _))) := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 f hf).hom_ext _ _ fun x ↦ ?_
  simp only [fromOfGlobalSections, toBasicOpenOfGlobalSections, CommRingCat.ofHom_comp,
    Category.assoc, Scheme.Cover.ι_glueMorphisms_assoc, basicOpenIsoSpec_inv_ι_assoc,
    awayι_toSpecZero, Iso.inv_comp_eq]
  simp only [openCoverOfMapIrrelevantEqTop,
    Scheme.openCoverOfIsOpenCover_f, Scheme.isoOfEq_hom_ι_assoc, ← morphismRestrict_ι_assoc]
  congr 1
  simp only [basicOpenIsoSpecAway, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← Iso.eq_inv_comp,
    IsOpenImmersion.isoOfRangeEq_inv_fac_assoc, ← HomogeneousLocalization.algebraMap_eq]
  congr 2
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq _ A,
    ← RingHom.comp_assoc, IsLocalization.map_comp, RingHom.comp_assoc]

end ofGlobalSection

end AlgebraicGeometry.Proj

