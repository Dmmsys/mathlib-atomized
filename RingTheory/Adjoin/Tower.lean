/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.Adjoin.FG

/-!
# Adjoining elements and being finitely generated in an algebra tower

## Main results

* `Algebra.fg_trans'`: if `S` is finitely generated as `R`-algebra and `A` as `S`-algebra,
  then `A` is finitely generated as `R`-algebra
* `fg_of_fg_of_fg`: **Artin--Tate lemma**: if C/B/A is a tower of rings, and A is Noetherian, and
  C is algebra-finite over A, and C is module-finite over B, then B is algebra-finite over A.
-/

public section


open scoped Pointwise

universe u v w u₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

namespace Algebra

/-
**Algebra.adjoin_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_restrictScalars (C D E : Type*) [CommSemiring C] [CommSemiring D] [
CommSemiring E] [Algebra C D] [Algebra C E] [Algebra D E] [IsScalarTower C D E] 
(S : Set E) : (Algebra.adjoin D S).restrictScalars C = (Algebra.adjoin ((⊤ : Sub
algebra C D).map (IsScalarTower.toAlgHom C D E)) S).restrictScalars C
参数：C D E : Type*；S : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subalgebra.setRange_algebraMap`：setRange_algebraMap {R A : Type*} [CommS
emiring R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A) : Set.range (alge
braMap S A) = (S : S…
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem adjoin_restrictScalars (C D E : Type*) [CommSemiring C] [CommSemiring D] [CommSemiring E]
    [Algebra C D] [Algebra C E] [Algebra D E] [IsScalarTower C D E] (S : Set E) :
    (Algebra.adjoin D S).restrictScalars C =
      (Algebra.adjoin ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) S).restrictScalars
        C := by
  suffices
    Set.range (algebraMap D E) =
      Set.range (algebraMap ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) E) by
    ext x
    change x ∈ Subsemiring.closure (_ ∪ S) ↔ x ∈ Subsemiring.closure (_ ∪ S)
    rw [this]
  simp
/-
**Algebra.adjoin_res_eq_adjoin_res** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_res_eq_adjoin_res (C D E F : Type*) [CommSemiring C] [CommSemiring 
D] [CommSemiring E] [CommSemiring F] [Algebra C D] [Algebra C E] [Algebra C F] [
Algebra D F] [Algebra E F] [IsScalarTower C D F] [IsScalarTower C E F] {S : Set 
D} {T : Set E} (hS : Algebra.adjoin C S = ⊤) (hT : Algebra.adjoin C T = ⊤) : (Al
gebra.adjoin E (algebraMap D F '' S)).restrictScalars C = (Algebra.adjoin D (alg
ebraMap E F '' T)).restrictScalars C
参数：C D E F : Type*；hS : Algebra.adjoin C S = ⊤；hT : Algebra.adjoin C T = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_restrictScalars`：adjoin_restrictScalars (C D E : Type*) [
CommSemiring C] [CommSemiring D] [CommSemiring E] [Algebra C D] [Algebra C E] [A
lgebra D E] [IsScala…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_image`：adjoin_image (f : A ->ₐ[R] B) (s : Set A) : adjoin
 R (f '' s) = (adjoin R s).map f
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.coe_toRingHom`：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) =
 f
· 使用定理 `IsScalarTower.coe_toAlgHom`：coe_toAlgHom : ↑(toAlgHom R S A) = algebraMa
p S A
· 使用定理 `Algebra.adjoin_union_eq_adjoin_adjoin`：adjoin_union_eq_adjoin_adjoin : a
djoin R (s union t) = (adjoin (adjoin R s) t).restrictScalars R
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
-/
theorem adjoin_res_eq_adjoin_res (C D E F : Type*) [CommSemiring C] [CommSemiring D]
    [CommSemiring E] [CommSemiring F] [Algebra C D] [Algebra C E] [Algebra C F] [Algebra D F]
    [Algebra E F] [IsScalarTower C D F] [IsScalarTower C E F] {S : Set D} {T : Set E}
    (hS : Algebra.adjoin C S = ⊤) (hT : Algebra.adjoin C T = ⊤) :
    (Algebra.adjoin E (algebraMap D F '' S)).restrictScalars C =
      (Algebra.adjoin D (algebraMap E F '' T)).restrictScalars C := by
  rw [adjoin_restrictScalars C E, adjoin_restrictScalars C D, ← hS, ← hT, ← Algebra.adjoin_image,
    ← Algebra.adjoin_image, ← AlgHom.coe_toRingHom, ← AlgHom.coe_toRingHom,
    IsScalarTower.coe_toAlgHom, IsScalarTower.coe_toAlgHom, ← adjoin_union_eq_adjoin_adjoin, ←
    adjoin_union_eq_adjoin_adjoin, Set.union_comm]

end Algebra

section

/-
**Algebra.fg_trans'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.fg_trans' {R S A : Type*} [CommSemiring R] [CommSemiring S] [Semir
ing A] [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] (hRS : (⊤
 : Subalgebra R S).FG) (hSA : (⊤ : Subalgebra S A).FG) : (⊤ : Subalgebra R A).FG
参数：hRS : (⊤ : Subalgebra R S).FG；hSA : (⊤ : Subalgebra S A).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Algebra.adjoin_algebraMap_image_union_eq_adjoin_adjoin`：adjoin_algebraMa
p_image_union_eq_adjoin_adjoin (s : Set S) (t : Set A) : adjoin R (algebraMap S 
A '' s union t) = (adjoin (adjoin R s) t).re…
· 使用定理 `Algebra.adjoin_top`：adjoin_top {A} [Semiring A] [Algebra S A] (t : Set A
) : adjoin (⊤ : Subalgebra R S) t = (adjoin S t).restrictScalars (⊤ : Subalgebra
 R S)
· 使用定理 `Subalgebra.restrictScalars_top`：restrictScalars_top : restrictScalars R 
(⊤ : Subalgebra S A) = ⊤
-/
theorem Algebra.fg_trans' {R S A : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] (hRS : (⊤ : Subalgebra R S).FG)
    (hSA : (⊤ : Subalgebra S A).FG) : (⊤ : Subalgebra R A).FG := by
  classical
  rcases hRS with ⟨s, hs⟩
  rcases hSA with ⟨t, ht⟩
  exact ⟨s.image (algebraMap S A) ∪ t, by
    rw [Finset.coe_union, Finset.coe_image,
        Algebra.adjoin_algebraMap_image_union_eq_adjoin_adjoin,
        hs, Algebra.adjoin_top, ht, Subalgebra.restrictScalars_top,
        Subalgebra.restrictScalars_top
       ]
    ⟩
end

section ArtinTate

variable (C : Type*)

section Semiring

variable [CommSemiring A] [CommSemiring B] [Semiring C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

open Finset Submodule

/-
**exists_subalgebra_of_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_subalgebra_of_fg (hAC : (⊤ : Subalgebra A C).FG) (hBC : (⊤ : Submod
ule B C).FG) : exists B₀ : Subalgebra A B, B₀.FG ∧ (⊤ : Submodule B₀ C).FG
参数：hAC : (⊤ : Subalgebra A C).FG；hBC : (⊤ : Submodule B C).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Finset.mem_image₂_of_mem`：mem_image₂_of_mem (ha : a in s) (hb : b in t) 
: f a b in image₂ f s t
· 使用定理 `Finset.mem_union_left`：mem_union_left (t : Finset α) (h : a in s) : a in
 s union t
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_mul_span`：span_mul_span : span R S * span R T = span R (S
 * T)
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Finset.mem_union_right`：mem_union_right (s : Finset α) (h : a in t) : a 
in s union t
· 使用定理 `Finset.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `Subalgebra.fg_adjoin_finset`：fg_adjoin_finset (s : Finset A) : (Algebra.
adjoin R (↑s : Set A)).FG
· 使用定理 `Submodule.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars S : Submodule R M -> Submodule S M)
· 使用定理 `Submodule.restrictScalars_top`：restrictScalars_top : restrictScalars S (
⊤ : Submodule R M) = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Algebra.top_toSubmodule`：top_toSubmodule : Subalgebra.toSubmodule (⊤ : S
ubalgebra R A) = ⊤
· 使用定理 `Algebra.adjoin_eq_span`：adjoin_eq_span : Subalgebra.toSubmodule (adjoin 
R s) = span R (Submonoid.closure s)
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
（共 33 条，此处仅展示前 30 条）
-/
theorem exists_subalgebra_of_fg (hAC : (⊤ : Subalgebra A C).FG) (hBC : (⊤ : Submodule B C).FG) :
    ∃ B₀ : Subalgebra A B, B₀.FG ∧ (⊤ : Submodule B₀ C).FG := by
  obtain ⟨x, hx⟩ := hAC
  obtain ⟨y, hy⟩ := hBC
  have := hy
  simp_rw [eq_top_iff', mem_span_finset] at this
  choose f _ hf using this
  classical
  let s : Finset B := Finset.image₂ f (x ∪ y * y) y
  have hxy :
    ∀ xi ∈ x, xi ∈ span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) :=
    fun xi hxi =>
    hf xi ▸
      sum_mem fun yj hyj =>
        smul_mem (span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C))
          ⟨f xi yj, Algebra.subset_adjoin <| mem_image₂_of_mem (mem_union_left _ hxi) hyj⟩
          (subset_span <| mem_insert_of_mem hyj)
  have hyy :
    span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) *
        span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) ≤
      span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) := by
    rw [span_mul_span, span_le, coe_insert]
    rintro _ ⟨yi, rfl | hyi, yj, rfl | hyj, rfl⟩ <;> dsimp
    · rw [mul_one]
      exact subset_span (Set.mem_insert _ _)
    · rw [one_mul]
      exact subset_span (Set.mem_insert_of_mem _ hyj)
    · rw [mul_one]
      exact subset_span (Set.mem_insert_of_mem _ hyi)
    · rw [← hf (yi * yj)]
      exact
        SetLike.mem_coe.2
          (sum_mem fun yk hyk =>
            smul_mem (span (Algebra.adjoin A (↑s : Set B)) (insert 1 ↑y : Set C))
              ⟨f (yi * yj) yk,
                Algebra.subset_adjoin <|
                  mem_image₂_of_mem (mem_union_right _ <| mul_mem_mul hyi hyj) hyk⟩
              (subset_span <| Set.mem_insert_of_mem _ hyk : yk ∈ _))
  refine ⟨Algebra.adjoin A (↑s : Set B), Subalgebra.fg_adjoin_finset _, insert 1 y, ?_⟩
  convert! restrictScalars_injective A (Algebra.adjoin A (s : Set B)) C _
  rw [restrictScalars_top, eq_top_iff, ← Algebra.top_toSubmodule, ← hx, Algebra.adjoin_eq_span,
    span_le]
  refine fun r hr =>
    Submonoid.closure_induction (fun c hc => hxy c hc) (subset_span <| mem_insert_self _ _)
      (fun p q _ _ hp hq => hyy <| Submodule.mul_mem_mul hp hq) hr

end Semiring

section Ring

variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- **Artin--Tate lemma**: if A ⊆ B ⊆ C is a chain of subrings of commutative rings, and
A is Noetherian, and C is algebra-finite over A, and C is module-finite over B,
then B is algebra-finite over A.

References: Atiyah--Macdonald Proposition 7.8; Altman--Kleiman 16.17. -/
@[stacks 00IS]
/-
**fg_of_fg_of_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fg_of_fg_of_fg [IsNoetherianRing A] (hAC : (⊤ : Subalgebra A C).FG) (hBC :
 (⊤ : Submodule B C).FG) (hBCi : Function.Injective (algebraMap B C)) : (⊤ : Sub
algebra A B).FG
参数：hAC : (⊤ : Subalgebra A C).FG；hBC : (⊤ : Submodule B C).FG；hBCi : Function.In
jective (algebraMap B C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_subalgebra_of_fg`：exists_subalgebra_of_fg (hAC : (⊤ : Subalgebra 
A C).FG) (hBC : (⊤ : Submodule B C).FG) : exists B₀ : Subalgebra A B, B₀.FG ∧ (⊤
 : Submodule …
· 使用定理 `Algebra.fg_trans'`：Algebra.fg_trans' {R S A : Type*} [CommSemiring R] [C
ommSemiring S] [Semiring A] [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarT
ower R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subalgebra.fg_top`：fg_top (S : Subalgebra R A) : (⊤ : Subalgebra R S).FG
 ↔ S.FG
· 使用定理 `Subalgebra.fg_of_submodule_fg`：fg_of_submodule_fg (h : (⊤ : Submodule R 
A).FG) : (⊤ : Subalgebra R A).FG
· 使用定理 `isNoetherianRing_of_fg`：isNoetherianRing_of_fg {S : Subalgebra R A} (HS 
: S.FG) [IsNoetherianRing R] : IsNoetherianRing S
· 使用定理 `fg_of_injective`：fg_of_injective [IsNoetherian S P] {N : Submodule R M} 
{σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : 
M ->ₛ…

--- 原说明 ---
**Artin--Tate lemma**: if A ⊆ B ⊆ C is a chain of subrings of commutative rings,
 and
A is Noetherian, and C is algebra-finite over A, and C is module-finite over B,
then B is algebra-finite over A.

References: Atiyah--Macdonald Proposition 7.8; Altman--Kleiman 16.17.
-/
theorem fg_of_fg_of_fg [IsNoetherianRing A] (hAC : (⊤ : Subalgebra A C).FG)
    (hBC : (⊤ : Submodule B C).FG) (hBCi : Function.Injective (algebraMap B C)) :
    (⊤ : Subalgebra A B).FG :=
  let ⟨B₀, hAB₀, hB₀C⟩ := exists_subalgebra_of_fg A B C hAC hBC
  Algebra.fg_trans' (B₀.fg_top.2 hAB₀) <|
    Subalgebra.fg_of_submodule_fg <|
      have : IsNoetherianRing B₀ := isNoetherianRing_of_fg hAB₀
      have : Module.Finite B₀ C := ⟨hB₀C⟩
      fg_of_injective (IsScalarTower.toAlgHom B₀ B C).toLinearMap hBCi

end Ring

end ArtinTate

