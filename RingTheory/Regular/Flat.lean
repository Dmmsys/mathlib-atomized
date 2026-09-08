/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Nailin Guan
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# `RingTheory.Sequence.IsWeaklyRegular` is stable under flat base change

## Main results
* `RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange`: Let `R` be a commutative ring,
  `M` be an `R`-module, `S` be a flat `R`-algebra, `N` be the base change of `M` to `S`.
  If `[r₁, …, rₙ]` is a weakly regular `M`-sequence, then its image in `N` is a weakly regular
  `N`-sequence.
-/

public section

namespace RingTheory.Sequence

open Module

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Let `R` be a commutative ring, `M` be an `R`-module, `S` be a flat `R`-algebra, `N` be the base
  change of `M` to `S`. If `[r₁, …, rₙ]` is a weakly regular `M`-sequence, then its image in `N` is
  a weakly regular `N`-sequence. -/
/-
**RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange** 是 Mathlib 中的一个定理
，位于命名空间 `RingTheory.Sequence.IsWeaklyRegular`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : CommRing S]   [inst_2 : Algebra R S] [inst_3 : AddCommGroup M]
 [inst_4 : _root_.Module R M] [inst_5 : AddCommGroup N]   [inst_6 : _root_.Modul
e R N] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] [Module.Flat 
R S]   {f : M →ₗ[R] N},   IsBaseChange S f →     ∀ {rs : List R},       RingTheo
ry.Sequence.IsWeaklyRegular M rs → RingTheory.Sequence.IsWeaklyRegular N (List.m
ap (⇑(algebraMap R S)) rs)
参数：List.map (⇑(algebraMap R S)) rs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsSMulRegular.of_flat_of_isBaseChange`：IsSMulRegular.of_flat_of_isBaseCh
ange {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {x : R} (reg : IsSMulRegular M x) 
: IsSMulRegular N (algebraM…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Let `R` be a commutative ring, `M` be an `R`-module, `S` be a flat `R`-algebra, 
`N` be the base
  change of `M` to `S`. If `[r₁, …, rₙ]` is a weakly regular `M`-sequence, then 
its image in `N` is
  a weakly regular `N`-sequence.
-/
theorem IsWeaklyRegular.of_flat_of_isBaseChange [Flat R S] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    {rs : List R} (reg : IsWeaklyRegular M rs) : IsWeaklyRegular N (rs.map (algebraMap R S)) := by
  induction rs generalizing M N with
  | nil => simp
  | cons x _ ih =>
    simp only [List.map_cons, isWeaklyRegular_cons_iff] at reg ⊢
    have e := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop x M S).symm ≪≫ₗ
      QuotSMulTop.congr ((algebraMap R S) x) hf.equiv
    have hg : IsBaseChange S <|
        e.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R S (QuotSMulTop x M) 1 :=
      IsBaseChange.of_equiv e (fun _ ↦ by simp)
    exact ⟨reg.1.of_flat_of_isBaseChange hf, ih hg reg.2⟩
/-
**RingTheory.Sequence.IsWeaklyRegular.of_flat** 是 Mathlib 中的一个定理，位于命名空间 `RingThe
ory.Sequence.IsWeaklyRegular`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] [Module.Flat R S]   {rs : List R},   RingTheory.Sequence.
IsWeaklyRegular R rs → RingTheory.Sequence.IsWeaklyRegular S (List.map (⇑(algebr
aMap R S)) rs)
参数：List.map (⇑(algebraMap R S)) rs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange`：∀ {R : Type
 u_1} {S : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 :
 CommRing S]   [inst_2 : Algebra R S] [inst_3 : A…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsBaseChange.linearMap`：IsBaseChange.linearMap : IsBaseChange S (Algebra
.linearMap R S)
-/
theorem IsWeaklyRegular.of_flat [Flat R S] {rs : List R} (reg : IsWeaklyRegular R rs) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) :=
  reg.of_flat_of_isBaseChange (IsBaseChange.linearMap R S)

variable (S) (T : Submonoid R) [IsLocalization T S]
/-
**RingTheory.Sequence.IsWeaklyRegular.of_isLocalizedModule** 是 Mathlib 中的一个定理，位于
命名空间 `RingTheory.Sequence.IsWeaklyRegular`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : CommRing S]   [inst_2 : Algebra R S] [inst_3 : AddCommGroup M]
 [inst_4 : _root_.Module R M] [inst_5 : AddCommGroup N]   [inst_6 : _root_.Modul
e R N] [inst_7 : _root_.Module S N] [IsScalarTower R S N] (T : Submonoid R) [IsL
ocalization T S]   (f : M →ₗ[R] N) [IsLocalizedModule T f] {rs : List R},   Ring
Theory.Sequence.IsWeaklyRegular M rs → RingTheory.Sequence.IsWeaklyRegular N (Li
st.map (⇑(algebraMap R S)) rs)
参数：S : Type u_2；T : Submonoid R；f : M →ₗ[R] N；List.map (⇑(algebraMap R S)) rs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.flat`：IsLocalization.flat : Module.Flat R S
· 使用定理 `RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange`：∀ {R : Type
 u_1} {S : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 :
 CommRing S]   [inst_2 : Algebra R S] [inst_3 : A…
· 使用定理 `IsLocalizedModule.isBaseChange`：IsLocalizedModule.isBaseChange [IsLocali
zedModule S f] : IsBaseChange A f
-/
theorem IsWeaklyRegular.of_isLocalizedModule (f : M →ₗ[R] N) [IsLocalizedModule T f]
    {rs : List R} (reg : IsWeaklyRegular M rs) : IsWeaklyRegular N (rs.map (algebraMap R S)) :=
  have : Flat R S := IsLocalization.flat S T
  reg.of_flat_of_isBaseChange (IsLocalizedModule.isBaseChange T S f)

include T in
/-
**RingTheory.Sequence.IsWeaklyRegular.of_isLocalization** 是 Mathlib 中的一个定理，位于命名空
间 `RingTheory.Sequence.IsWeaklyRegular`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (T : Submonoid R)   [IsLocalization T S] {rs : List R},  
 RingTheory.Sequence.IsWeaklyRegular R rs → RingTheory.Sequence.IsWeaklyRegular 
S (List.map (⇑(algebraMap R S)) rs)
参数：S : Type u_2；T : Submonoid R；List.map (⇑(algebraMap R S)) rs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingTheory.Sequence.IsWeaklyRegular.of_isLocalizedModule`：∀ {R : Type u_
1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : Co
mmRing S]   [inst_2 : Algebra R S] [inst_3 : A…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
-/
theorem IsWeaklyRegular.of_isLocalization {rs : List R} (reg : IsWeaklyRegular R rs) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) :=
  reg.of_isLocalizedModule S T (Algebra.linearMap R S)

variable (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p]
/-
**RingTheory.Sequence.IsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem** 是 
Mathlib 中的一个定理，位于命名空间 `RingTheory.Sequence.IsWeaklyRegular`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : CommRing S]   [inst_2 : Algebra R S] [inst_3 : AddCommGroup M]
 [inst_4 : _root_.Module R M] [inst_5 : AddCommGroup N]   [inst_6 : _root_.Modul
e R N] [inst_7 : _root_.Module S N] [IsScalarTower R S N] (p : Ideal R) [inst_9 
: p.IsPrime]   [IsLocalization.AtPrime S p] [Nontrivial N] [Module.Finite S N] (
f : M →ₗ[R] N) [IsLocalizedModule.AtPrime p f]   {rs : List R},   RingTheory.Seq
uence.IsWeaklyRegular M rs →     (∀ r ∈ rs, r ∈ p) → RingTheory.Sequence.IsRegul
ar N (List.map (⇑(algebraMap R S)) rs)
参数：S : Type u_2；p : Ideal R；f : M →ₗ[R] N；∀ r ∈ rs, r ∈ p；List.map (⇑(algebraMap
 R S)) rs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal`：∀ {R :
 Type u_1} {M : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 
: _root_.Module R M]   [inst_3 : IsLocalRing R] [Nontr…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.AtPrime.to_map_mem_maximal_iff`：to_map_mem_maximal_iff (x
 : R) (h : IsLocalRing S
· 使用定理 `RingTheory.Sequence.IsWeaklyRegular.of_isLocalizedModule`：∀ {R : Type u_
1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : Co
mmRing S]   [inst_2 : Algebra R S] [inst_3 : A…
-/
theorem IsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem
    [Nontrivial N] [Module.Finite S N] (f : M →ₗ[R] N) [IsLocalizedModule.AtPrime p f]
    {rs : List R} (reg : IsWeaklyRegular M rs) (mem : ∀ r ∈ rs, r ∈ p) :
    IsRegular N (rs.map (algebraMap R S)) := by
  have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
  refine (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (fun _ hr ↦ ?_)).mpr <|
    reg.of_isLocalizedModule S p.primeCompl f
  rcases List.mem_map.mp hr with ⟨r, hr, eq⟩
  simpa only [← eq, IsLocalization.AtPrime.to_map_mem_maximal_iff S p] using mem r hr
/-
**RingTheory.Sequence.IsWeaklyRegular.isRegular_of_isLocalization_of_mem** 是 Mat
hlib 中的一个定理，位于命名空间 `RingTheory.Sequence.IsWeaklyRegular`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (p : Ideal R)   [inst_3 : p.IsPrime] [IsLocalization.AtPr
ime S p] {rs : List R},   RingTheory.Sequence.IsWeaklyRegular R rs →     (∀ r ∈ 
rs, r ∈ p) → RingTheory.Sequence.IsRegular S (List.map (⇑(algebraMap R S)) rs)
参数：S : Type u_2；p : Ideal R；∀ r ∈ rs, r ∈ p；List.map (⇑(algebraMap R S)) rs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.AtPrime.nontrivial`：∀ {R : Type u_1} [inst : CommSemiring
 R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal R
)   [hp : P.IsPrime] [I…
· 使用定理 `RingTheory.Sequence.IsWeaklyRegular.isRegular_of_isLocalizedModule_of_me
m`：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : CommRin
g R] [inst_1 : CommRing S]   [inst_2 : Algebra R S] [inst_3 : A…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
-/
theorem IsWeaklyRegular.isRegular_of_isLocalization_of_mem
    {rs : List R} (reg : IsWeaklyRegular R rs) (mem : ∀ r ∈ rs, r ∈ p) :
    IsRegular S (rs.map (algebraMap R S)) :=
  have : Nontrivial S := IsLocalization.AtPrime.nontrivial S p
  reg.isRegular_of_isLocalizedModule_of_mem S p (Algebra.linearMap R S) mem

variable {S} [FaithfullyFlat R S]

/-- Let `R` be a commutative ring, `M` be an `R`-module, `S` be a faithfully flat `R`-algebra,
  `N` be the base change of `M` to `S`. If `[r₁, …, rₙ]` is a regular `M`-sequence, then its image
  in `N` is a regular `N`-sequence. -/
/-
**RingTheory.Sequence.IsRegular.of_faithfullyFlat_of_isBaseChange** 是 Mathlib 中的
一个定理，位于命名空间 `RingTheory.Sequence.IsRegular`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : CommRing S]   [inst_2 : Algebra R S] [inst_3 : AddCommGroup M]
 [inst_4 : _root_.Module R M] [inst_5 : AddCommGroup N]   [inst_6 : _root_.Modul
e R N] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] [Module.Faith
fullyFlat R S]   {f : M →ₗ[R] N},   IsBaseChange S f →     ∀ {rs : List R},     
  RingTheory.Sequence.IsRegular M rs → RingTheory.Sequence.IsRegular N (List.map
 (⇑(algebraMap R S)) rs)
参数：List.map (⇑(algebraMap R S)) rs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange`：∀ {R : Type
 u_1} {S : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 :
 CommRing S]   [inst_2 : Algebra R S] [inst_3 : A…
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `RingTheory.Sequence.IsRegular.toIsWeaklyRegular`：∀ {R : Type u_1} {M : T
ype u_3} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R
 M]   {rs : List R}, RingTheory.Seque…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_ofList`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring R] [i
nst_1 : Semiring S] (f : R →+* S) (rs : List R),   Ideal.map f (Ideal.ofList rs)
 = Ide…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsBaseChange.map_smul_top_ne_top_iff_of_faithfullyFlat`：∀ (R : Type u) (
M : Type v) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Modul
e R M] {S : Type u_1}   {N : Type u_2} [inst…
· 使用定理 `RingTheory.Sequence.IsRegular.top_ne_smul`：∀ {R : Type u_1} {M : Type u_
3} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   
{rs : List R}, RingTheory.Seque…

--- 原说明 ---
Let `R` be a commutative ring, `M` be an `R`-module, `S` be a faithfully flat `R
`-algebra,
  `N` be the base change of `M` to `S`. If `[r₁, …, rₙ]` is a regular `M`-sequen
ce, then its image
  in `N` is a regular `N`-sequence.
-/
theorem IsRegular.of_faithfullyFlat_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    {rs : List R} (reg : IsRegular M rs) : IsRegular N (rs.map (algebraMap R S)) := by
  refine ⟨reg.1.of_flat_of_isBaseChange hf, ?_⟩
  rw [← Ideal.map_ofList]
  exact ((hf.map_smul_top_ne_top_iff_of_faithfullyFlat R M _).mpr reg.2.symm).symm
/-
**RingTheory.Sequence.IsRegular.of_faithfullyFlat** 是 Mathlib 中的一个定理，位于命名空间 `Rin
gTheory.Sequence.IsRegular`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Module.FaithfullyFlat R S] {rs : List R},   RingTheory
.Sequence.IsRegular R rs → RingTheory.Sequence.IsRegular S (List.map (⇑(algebraM
ap R S)) rs)
参数：List.map (⇑(algebraMap R S)) rs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingTheory.Sequence.IsRegular.of_faithfullyFlat_of_isBaseChange`：∀ {R : 
Type u_1} {S : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst
_1 : CommRing S]   [inst_2 : Algebra R S] [inst_3 : A…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsBaseChange.linearMap`：IsBaseChange.linearMap : IsBaseChange S (Algebra
.linearMap R S)
-/
theorem IsRegular.of_faithfullyFlat {rs : List R} (reg : IsRegular R rs) :
    IsRegular S (rs.map (algebraMap R S)) :=
  reg.of_faithfullyFlat_of_isBaseChange (IsBaseChange.linearMap R S)

end RingTheory.Sequence

