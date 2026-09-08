/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jung Tao Cheng, Christian Merten, Andrew Yang
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Submersive

/-!
# Standard smooth algebras

A standard smooth algebra is an algebra that admits a `SubmersivePresentation`. A standard
smooth algebra is of relative dimension `n` if it admits a submersive presentation of
dimension `n`.

While every standard smooth algebra is smooth, the converse does not hold. But if `S` is `R`-smooth,
then `S` is `R`-standard smooth locally on `S`, i.e. there exists a set `{ t }` of `S` that
generates the unit ideal, such that `Sₜ` is `R`-standard smooth for every `t` (TODO, see below).

## Main definitions

All of these are in the `Algebra` namespace. Let `S` be an `R`-algebra.

- `Algebra.IsStandardSmooth`: `S` is `R`-standard smooth if `S` admits a submersive
  `R`-presentation.
- `Algebra.IsStandardSmooth.relativeDimension`: If `S` is `R`-standard smooth this is the dimension
  of an arbitrary submersive `R`-presentation of `S`. This is independent of the choice
  of the presentation (TODO, see below).
- `Algebra.IsStandardSmoothOfRelativeDimension n`: `S` is `R`-standard smooth of relative dimension
  `n` if it admits a submersive `R`-presentation of dimension `n`.

## TODO

- Show that locally on the target, smooth algebras are standard smooth.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

@[expose] public section

universe t t' w w' u v

open TensorProduct Module MvPolynomial

variable (n m : ℕ)

namespace Algebra

variable (R : Type u) (S : Type v) (ι : Type w) (σ : Type t) [CommRing R] [CommRing S] [Algebra R S]

attribute [local instance] Fintype.ofFinite

/--
An `R`-algebra `S` is called standard smooth, if there
exists a submersive presentation.
-/
/-
**Algebra.IsStandardSmooth** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u) → (S : Type v) → [inst : CommRing R] → [inst_1 : CommRing S] 
→ [Algebra R S] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-algebra `S` is called standard smooth, if there
exists a submersive presentation.
-/
class IsStandardSmooth : Prop where
  out : ∃ (ι σ : Type) (_ : Finite σ), Finite ι ∧ Nonempty (SubmersivePresentation R S ι σ)

variable [Finite σ]

variable {R S ι σ} in
/-
**Algebra.SubmersivePresentation.isStandardSmooth** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebra.SubmersivePresentation`。
形式化陈述：∀ {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [inst : CommRing R] 
[inst_1 : CommRing S] [inst_2 : Algebra R S]   [inst_3 : Finite σ] [Finite ι] (P
 : Algebra.SubmersivePresentation R S ι σ), Algebra.IsStandardSmooth R S
参数：P : Algebra.SubmersivePresentation R S ι σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma SubmersivePresentation.isStandardSmooth [Finite ι] (P : SubmersivePresentation R S ι σ) :
    IsStandardSmooth R S := by
  exact ⟨_, _, _, inferInstance, ⟨P.reindex (Fintype.equivFin _).symm (Fintype.equivFin _).symm⟩⟩

/--
The relative dimension of a standard smooth `R`-algebra `S` is
the dimension of an arbitrarily chosen submersive `R`-presentation of `S`.

Note: If `S` is non-trivial, this number is independent of the choice of the presentation as it is
equal to the `S`-rank of `Ω[S/R]`
(see `IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`).
-/
/-
**Algebra.IsStandardSmooth.relativeDimension** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.
IsStandardSmooth`。
形式化陈述：(R : Type u) →   (S : Type v) →     [inst : CommRing R] → [inst_1 : CommRi
ng S] → [inst_2 : Algebra R S] → [Algebra.IsStandardSmooth R S] → ℕ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsStandardSmooth.out`：∀ {R : Type u} {S : Type v} {inst : CommRi
ng R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   [self : Algebra.IsStandardS
mooth R S],   ∃ ι …

--- 原说明 ---
The relative dimension of a standard smooth `R`-algebra `S` is
the dimension of an arbitrarily chosen submersive `R`-presentation of `S`.

Note: If `S` is non-trivial, this number is independent of the choice of the pre
sentation as it is
equal to the `S`-rank of `Ω[S/R]`
(see `IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`).
-/
noncomputable def IsStandardSmooth.relativeDimension [IsStandardSmooth R S] : ℕ :=
  letI := ‹IsStandardSmooth R S›.out.choose_spec.choose_spec.choose
  ‹IsStandardSmooth R S›.out.choose_spec.choose_spec.choose_spec.2.some.dimension

/--
An `R`-algebra `S` is called standard smooth of relative dimension `n`, if there exists
a submersive presentation of dimension `n`.
-/
/-
**Algebra.IsStandardSmoothOfRelativeDimension** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algeb
ra`。
形式化陈述：ℕ → (R : Type u) → (S : Type v) → [inst : CommRing R] → [inst_1 : CommRing
 S] → [Algebra R S] → Prop
参数：R : Type u；S : Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-algebra `S` is called standard smooth of relative dimension `n`, if there
 exists
a submersive presentation of dimension `n`.
-/
class IsStandardSmoothOfRelativeDimension : Prop where
  out : ∃ (ι σ : Type) (_ : Finite σ) (_ : Finite ι) (P : SubmersivePresentation R S ι σ),
    P.dimension = n

variable {R S ι σ n} in
/-
**Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension** 是 Mathlib
 中的一个定理，位于命名空间 `Algebra.SubmersivePresentation`。
形式化陈述：∀ {n : ℕ} {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [inst : Comm
Ring R] [inst_1 : CommRing S]   [inst_2 : Algebra R S] [inst_3 : Finite σ] [Fini
te ι] (P : Algebra.SubmersivePresentation R S ι σ),   P.dimension = n → Algebra.
IsStandardSmoothOfRelativeDimension n R S
参数：P : Algebra.SubmersivePresentation R S ι σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.SubmersivePresentation.reindex_toPreSubmersivePresentation`：∀ {R
 : Type u} {S : Type v} {ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : 
CommRing S] [inst_2 : Algebra R S]   [inst_3 : Finite σ]…
· 使用定理 `Algebra.PreSubmersivePresentation.reindex_toPresentation`：∀ {R : Type u}
 {S : Type v} {ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S
] [inst_2 : Algebra R S]   (P : Algebra.PreSub…
· 使用引理 `Algebra.Presentation.dimension_reindex`：dimension_reindex (P : Presentat
ion R S ι σ) {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ) : (P.reindex e f).dimensi
on = P.dimension
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma SubmersivePresentation.isStandardSmoothOfRelativeDimension [Finite ι]
    (P : SubmersivePresentation R S ι σ) (hP : P.dimension = n) :
    IsStandardSmoothOfRelativeDimension n R S := by
  refine ⟨⟨_, _, _, inferInstance,
    P.reindex (Fintype.equivFin _).symm (Fintype.equivFin σ).symm, ?_⟩⟩
  simp [hP]

variable {R} {S}
/-
**Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth** 是 Mathlib 中的一个定
理，位于命名空间 `Algebra.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ (n : ℕ) {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing
 S] [inst_2 : Algebra R S]   [H : Algebra.IsStandardSmoothOfRelativeDimension n 
R S], Algebra.IsStandardSmooth R S
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsStandardSmoothOfRelativeDimension.out`：∀ {n : ℕ} {R : Type u} 
{S : Type v} {inst : CommRing R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   
[self : Algebra.IsStandardSmoothOfRel…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
-/
lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth
    [H : IsStandardSmoothOfRelativeDimension n R S] : IsStandardSmooth R S :=
  ⟨_, _, _, H.out.choose_spec.choose_spec.choose_spec.choose,
    H.out.choose_spec.choose_spec.choose_spec.choose_spec.nonempty⟩
/-
**Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective** 是 Mathli
b 中的一个定理，位于命名空间 `Algebra.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S],   Function.Bijective ⇑(algebraMap R S) → Algebra.IsStandardS
moothOfRelativeDimension 0 R S
参数：algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `Algebra.Presentation.ofBijectiveAlgebraMap_dimension`：ofBijectiveAlgebra
Map_dimension (h : Function.Bijective (algebraMap R S)) : (ofBijectiveAlgebraMap
 h).dimension = 0
-/
lemma IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective
    (h : Function.Bijective (algebraMap R S)) :
    IsStandardSmoothOfRelativeDimension 0 R S :=
  ⟨_, _, _, inferInstance,
    SubmersivePresentation.ofBijectiveAlgebraMap h, Presentation.ofBijectiveAlgebraMap_dimension h⟩

variable (R) in
/-
**Algebra.IsStandardSmoothOfRelativeDimension.id** 是 Mathlib 中的一个定理，位于命名空间 `Alge
bra.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ (R : Type u) [inst : CommRing R], Algebra.IsStandardSmoothOfRelativeDime
nsion 0 R R
参数：R : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective`：∀ {
R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Alg
ebra R S],   Function.Bijective ⇑(algebraMap R S) → Algeb…
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
instance IsStandardSmoothOfRelativeDimension.id :
    IsStandardSmoothOfRelativeDimension 0 R R :=
  IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective Function.bijective_id
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsStandardSmooth.finitePresentation [IsStandardSmooth R S] :
    FinitePresentation R S := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact P.finitePresentation_of_isFinite
/-
**Algebra.IsStandardSmooth.of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsStan
dardSmooth`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {T : Type u_1}   [inst_3 : CommRing T] [inst_4 : Algebra R T]
 (e : S ≃ₐ[R] T) [Algebra.IsStandardSmooth R S],   Algebra.IsStandardSmooth R T
参数：e : S ≃ₐ[R] T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.SubmersivePresentation.isStandardSmooth`：∀ {R : Type u} {S : Typ
e v} {ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2
 : Algebra R S]   [inst_3 : Finite σ]…
-/
lemma IsStandardSmooth.of_algEquiv {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T)
    [IsStandardSmooth R S] : IsStandardSmooth R T := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact (P.ofAlgEquiv e).isStandardSmooth
/-
**Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv** 是 Mathlib 中的一个定理，位于命
名空间 `Algebra.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ (n : ℕ) {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing
 S] [inst_2 : Algebra R S] {T : Type u_1}   [inst_3 : CommRing T] [inst_4 : Alge
bra R T] (e : S ≃ₐ[R] T) [Algebra.IsStandardSmoothOfRelativeDimension n R S],   
Algebra.IsStandardSmoothOfRelativeDimension n R T
参数：n : ℕ；e : S ≃ₐ[R] T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension`：∀ {n
 : ℕ} {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [inst : CommRing R] [i
nst_1 : CommRing S]   [inst_2 : Algebra R S] [inst_3 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.SubmersivePresentation.ofAlgEquiv_toPreSubmersivePresentation`：∀
 {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : Algebra R S]   [inst_3 : Finite σ]…
· 使用定理 `Algebra.PreSubmersivePresentation.ofAlgEquiv_toPresentation`：∀ {R : Type
 u} {S : Type v} {ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRin
g S] [inst_2 : Algebra R S]   (P : Algebra.PreSub…
-/
lemma IsStandardSmoothOfRelativeDimension.of_algEquiv {T : Type*} [CommRing T] [Algebra R T]
    (e : S ≃ₐ[R] T) [IsStandardSmoothOfRelativeDimension n R S] :
    IsStandardSmoothOfRelativeDimension n R T := by
  obtain ⟨_, _, _, _, ⟨P, hP⟩⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
  exact (P.ofAlgEquiv e).isStandardSmoothOfRelativeDimension (by simpa)

section Composition

variable (R S T) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-
**Algebra.IsStandardSmooth.trans** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsStandardSm
ooth`。
形式化陈述：∀ (R : Type u) (S : Type v) [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (T : Type u_1)   [inst_3 : CommRing T] [inst_4 : Algebra R T]
 [inst_5 : Algebra S T] [IsScalarTower R S T]   [Algebra.IsStandardSmooth R S] [
Algebra.IsStandardSmooth S T], Algebra.IsStandardSmooth R T
参数：R : Type u；S : Type v；T : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
-/
lemma IsStandardSmooth.trans [IsStandardSmooth R S] [IsStandardSmooth S T] :
    IsStandardSmooth R T where
  out := by
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
    obtain ⟨_, _, _, _, ⟨Q⟩⟩ := ‹IsStandardSmooth S T›
    exact ⟨_, _, _, inferInstance, ⟨Q.comp P⟩⟩
/-
**Algebra.IsStandardSmoothOfRelativeDimension.trans** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebra.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ (n m : ℕ) (R : Type u) (S : Type v) [inst : CommRing R] [inst_1 : CommRi
ng S] [inst_2 : Algebra R S] (T : Type u_1)   [inst_3 : CommRing T] [inst_4 : Al
gebra R T] [inst_5 : Algebra S T] [IsScalarTower R S T]   [Algebra.IsStandardSmo
othOfRelativeDimension n R S] [Algebra.IsStandardSmoothOfRelativeDimension m S T
],   Algebra.IsStandardSmoothOfRelativeDimension (m + n) R T
参数：n m : ℕ；R : Type u；S : Type v；T : Type u_1；m + n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用引理 `Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimens
ion`：dimension_comp_eq_dimension_add_dimension [Finite ι] [Finite ι'] [Finite σ]
 [Finite σ'] : (Q.comp P).dimension = Q.dimension + P.dimension
-/
lemma IsStandardSmoothOfRelativeDimension.trans [IsStandardSmoothOfRelativeDimension n R S]
    [IsStandardSmoothOfRelativeDimension m S T] :
    IsStandardSmoothOfRelativeDimension (m + n) R T where
  out := by
    obtain ⟨_, _, _, _, P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    obtain ⟨_, _, _, _, Q, hQ⟩ := ‹IsStandardSmoothOfRelativeDimension m S T›
    refine ⟨_, _, _, inferInstance, Q.comp P, hP ▸ hQ ▸ ?_⟩
    apply PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension

end Composition

/-
**Algebra.IsStandardSmooth.localization_away** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
IsStandardSmooth`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (r : R)   [IsLocalization.Away r S], Algebra.IsStandardSmooth
 R S
参数：r : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma IsStandardSmooth.localization_away (r : R) [IsLocalization.Away r S] :
    IsStandardSmooth R S where
  out := ⟨_, _, _, inferInstance, ⟨SubmersivePresentation.localizationAway S r⟩⟩
/-
**Algebra.IsStandardSmoothOfRelativeDimension.localization_away** 是 Mathlib 中的一个
定理，位于命名空间 `Algebra.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (r : R)   [IsLocalization.Away r S], Algebra.IsStandardSmooth
OfRelativeDimension 0 R S
参数：r : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `Algebra.Presentation.localizationAway_dimension_zero`：localizationAway_d
imension_zero : (localizationAway S r).dimension = 0
-/
lemma IsStandardSmoothOfRelativeDimension.localization_away (r : R) [IsLocalization.Away r S] :
    IsStandardSmoothOfRelativeDimension 0 R S where
  out := ⟨_, _, _, inferInstance, SubmersivePresentation.localizationAway S r,
    Presentation.localizationAway_dimension_zero r⟩

section BaseChange

variable (T) [CommRing T] [Algebra R T]

/-
**Algebra.IsStandardSmooth.baseChange** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsStand
ardSmooth`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (T : Type u_1)   [inst_3 : CommRing T] [inst_4 : Algebra R T]
 [Algebra.IsStandardSmooth R S],   Algebra.IsStandardSmooth T (TensorProduct R T
 S)
参数：T : Type u_1；TensorProduct R T S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance IsStandardSmooth.baseChange [IsStandardSmooth R S] :
    IsStandardSmooth T (T ⊗[R] S) where
  out := by
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
    exact ⟨ι, σ, _, inferInstance, ⟨P.baseChange T⟩⟩
/-
**Algebra.IsStandardSmoothOfRelativeDimension.baseChange** 是 Mathlib 中的一个定理，位于命名
空间 `Algebra.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ (n : ℕ) {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing
 S] [inst_2 : Algebra R S] (T : Type u_1)   [inst_3 : CommRing T] [inst_4 : Alge
bra R T] [Algebra.IsStandardSmoothOfRelativeDimension n R S],   Algebra.IsStanda
rdSmoothOfRelativeDimension n T (TensorProduct R T S)
参数：n : ℕ；T : Type u_1；TensorProduct R T S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance IsStandardSmoothOfRelativeDimension.baseChange
    [IsStandardSmoothOfRelativeDimension n R S] :
    IsStandardSmoothOfRelativeDimension n T (T ⊗[R] S) where
  out := by
    obtain ⟨_, _, _, _, P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    exact ⟨_, _, _, inferInstance, P.baseChange T, hP⟩

end BaseChange

@[nontriviality]
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [Subsingleton S] : IsStandardSmooth R S :=
  ⟨Unit, Unit, inferInstance, inferInstance, ⟨.ofSubsingleton R S⟩⟩

@[nontriviality]
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [Subsingleton S] : IsStandardSmoothOfRelativeDimension 0 R S :=
  ⟨Unit, Unit, inferInstance, inferInstance, .ofSubsingleton R S, by simp [Presentation.dimension]⟩

end Algebra

