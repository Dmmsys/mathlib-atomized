/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Basic Properties of Complete Local Ring

In this file we prove that for local ring `R` with finitely generated maximal ideal,
`AdicCompletion (IsLocalRing.maximalIdeal R) R` is local ring with maximal ideal equal to
`IsLocalRing.maximalIdeal R` mapped by algebra map. Furthermore, it is complete with respect to
its maximal ideal.

As a corollary, for Noetherian local ring `R`, `AdicCompletion (maximalIdeal R) R` is always
a complete Noetherian local ring.

Most results needing finitely generation of maximal ideal have a version for Noetherian ring without
this side condition for convenience.

# Main Results

* `AdicCompletion.isLocalRing_of_fg` : for a local ring `R` with finitely generated maximal ideal,
  its completion with respect to `IsLocalRing.maximalIdeal R` is local ring.

* `AdicCompletion.maximalIdeal_eq_map_of_fg` : for a local ring `R` with finitely generated
  maximal ideal, the maximal ideal of its completion with respect to `IsLocalRing.maximalIdeal R`
  is equal to `IsLocalRing.maximalIdeal R` mapped by algebra map.

* `AdicCompletion.isAdicComplete_of_fg` : for a local ring `R` with finitely generated
  maximal ideal, `AdicCompletion (IsLocalRing.maximalIdeal R) R` itself is complete with respect to
  its maximal ideal.

* `AdicCompletion.spanFinrank_maximalIdeal_eq` : for Noetherian local ring `R`, minimal number of
  generators of maximal ideal of `R` and `AdicCompletion (IsLocalRing.maximalIdeal R) R` are equal.

-/

public section

variable {R : Type*} [CommRing R]

open Ideal Quotient

/-
**isLocalRing_of_isAdicComplete_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalRing_of_isAdicComplete_maximal (m : Ideal R) [m.IsMaximal] [IsAdicC
omplete m R] : IsLocalRing R
参数：m : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.of_unique_max_ideal`：of_unique_max_ideal (h : exists! I : Id
eal R, I.IsMaximal) : IsLocalRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsAdicComplete.le_jacobson_bot`：le_jacobson_bot [IsAdicComplete I R] : I
 <= (⊥ : Ideal R).jacobson
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem isLocalRing_of_isAdicComplete_maximal (m : Ideal R) [m.IsMaximal] [IsAdicComplete m R] :
    IsLocalRing R :=
  IsLocalRing.of_unique_max_ideal ⟨m, ‹m.IsMaximal›, fun _ hJ ↦
    (‹m.IsMaximal›.eq_of_le hJ.ne_top <|
      (IsAdicComplete.le_jacobson_bot m).trans <| sInf_le ⟨bot_le, hJ⟩).symm⟩

open IsLocalRing

namespace AdicCompletion

variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

/-
**AdicCompletion.isAdicComplete_self** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：isAdicComplete_self (fg : I.FG) : IsAdicComplete (I.map (algebraMap R (Adi
cCompletion I R))) (AdicCompletion I R)
参数：fg : I.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsAdicComplete.map_algebraMap_iff`：map_algebraMap_iff [CommRing S] [Modu
le S M] [Algebra R S] [IsScalarTower R S M] : IsAdicComplete (I.map (algebraMap 
R S)) M ↔ IsAdicComplet…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AdicCompletion.isAdicComplete`：isAdicComplete (h : I.FG) : IsAdicComplet
e I (AdicCompletion I M) where prec' x hx
-/
lemma isAdicComplete_self (fg : I.FG) :
    IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) :=
  (IsAdicComplete.map_algebraMap_iff _ _).mpr (AdicCompletion.isAdicComplete fg)
/-
**AdicCompletion.isMaximal_map_of_le** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：isMaximal_map_of_le (m : Ideal R) [m.IsMaximal] (le : I <= m) (fg : I.FG) 
: (m.map (algebraMap R (AdicCompletion I R))).IsMaximal
参数：m : Ideal R；le : I <= m；fg : I.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk`：evalOneₐ_comp_algebraMap_
eq_mk : (AdicCompletion.evalOneₐ I).toRingHom.comp (algebraMap R (AdicCompletion
 I R)) = (Ideal.Quotient.mk I)
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用引理 `Ideal.comap_map_of_surjective'`：comap_map_of_surjective' (f : F) (hf : F
unction.Surjective f) (I : Ideal R) : (I.map f).comap f = I ⊔ RingHom.ker f
· 使用引理 `AdicCompletion.evalOneₐ_surjective`：evalOneₐ_surjective : Function.Surje
ctive (evalOneₐ I)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用引理 `AdicCompletion.ker_evalOneₐ_eq_map`：ker_evalOneₐ_eq_map (fg : I.FG) : Ri
ngHom.ker (evalOneₐ I).toRingHom = I.map (algebraMap R (AdicCompletion I R))
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `Ideal.IsMaximal.map_of_surjective_of_ker_le`：∀ {R : Type u_1} {S : Type 
u_2} {F : Type u_3} [inst : Ring R] [inst_1 : Ring S] [inst_2 : FunLike F R S]  
 [rc : RingHomClass F R S] {f : F…
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Ideal.comap_isMaximal_of_surjective`：comap_isMaximal_of_surjective (hf :
 Function.Surjective f) {K : Ideal S} [H : IsMaximal K] : IsMaximal (comap f K)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
lemma isMaximal_map_of_le (m : Ideal R) [m.IsMaximal] (le : I ≤ m) (fg : I.FG) :
    (m.map (algebraMap R (AdicCompletion I R))).IsMaximal := by
  have mapeq : m.map (algebraMap R (AdicCompletion I R)) = (m.map (Ideal.Quotient.mk I)).comap
    (AdicCompletion.evalOneₐ I).toRingHom := by
    rw [← AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk, ← Ideal.map_map,
      Ideal.comap_map_of_surjective' (evalOneₐ I).toRingHom (evalOneₐ_surjective I),
      eq_comm, sup_eq_left, AdicCompletion.ker_evalOneₐ_eq_map I fg]
    exact Ideal.map_mono le
  have : (Ideal.map (Ideal.Quotient.mk I) m).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using le)
  rw [mapeq]
  exact Ideal.comap_isMaximal_of_surjective _ (evalOneₐ_surjective I)
/-
**AdicCompletion.isLocalRing_of_fg** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：isLocalRing_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) : IsLocalRing
 (AdicCompletion (maximalIdeal R) R)
参数：fg : (maximalIdeal R).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AdicCompletion.isMaximal_map_of_le`：isMaximal_map_of_le (m : Ideal R) [m
.IsMaximal] (le : I <= m) (fg : I.FG) : (m.map (algebraMap R (AdicCompletion I R
))).IsMaximal
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `AdicCompletion.isAdicComplete_self`：isAdicComplete_self (fg : I.FG) : Is
AdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R)
· 使用定理 `isLocalRing_of_isAdicComplete_maximal`：isLocalRing_of_isAdicComplete_max
imal (m : Ideal R) [m.IsMaximal] [IsAdicComplete m R] : IsLocalRing R
-/
lemma isLocalRing_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    IsLocalRing (AdicCompletion (maximalIdeal R) R) := by
  have := AdicCompletion.isMaximal_map_of_le _ _ (le_refl _) fg
  have := AdicCompletion.isAdicComplete_self _ fg
  exact isLocalRing_of_isAdicComplete_maximal
    ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)))
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsNoetherianRing R] [IsLocalRing R] : IsLocalRing (AdicCompletion (maximalIdeal R) R) :=
  AdicCompletion.isLocalRing_of_fg (fg_of_isNoetherianRing (maximalIdeal R))
/-
**AdicCompletion.maximalIdeal_eq_map_of_fg** 是 Mathlib 中的一个引理，位于命名空间 `AdicComple
tion`。
形式化陈述：maximalIdeal_eq_map_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) : hav
eI
参数：fg : (maximalIdeal R).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AdicCompletion.isLocalRing_of_fg`：isLocalRing_of_fg [IsLocalRing R] (fg 
: (maximalIdeal R).FG) : IsLocalRing (AdicCompletion (maximalIdeal R) R)
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用引理 `AdicCompletion.isMaximal_map_of_le`：isMaximal_map_of_le (m : Ideal R) [m
.IsMaximal] (le : I <= m) (fg : I.FG) : (m.map (algebraMap R (AdicCompletion I R
))).IsMaximal
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma maximalIdeal_eq_map_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    haveI := AdicCompletion.isLocalRing_of_fg fg
    maximalIdeal (AdicCompletion (maximalIdeal R) R) =
    (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  haveI := AdicCompletion.isLocalRing_of_fg fg
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ (le_refl _) fg)).symm
/-
**AdicCompletion.maximalIdeal_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：maximalIdeal_eq_map [IsNoetherianRing R] [IsLocalRing R] : maximalIdeal (A
dicCompletion (maximalIdeal R) R) = (maximalIdeal R).map (algebraMap R (AdicComp
letion (maximalIdeal R) R))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AdicCompletion.instIsLocalRingMaximalIdealOfIsNoetherianRing`：∀ {R : Typ
e u_1} [inst : CommRing R] [IsNoetherianRing R] [inst_2 : IsLocalRing R],   IsLo
calRing (AdicCompletion (IsLocalRing.maximalIdeal …
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用引理 `AdicCompletion.isMaximal_map_of_le`：isMaximal_map_of_le (m : Ideal R) [m
.IsMaximal] (le : I <= m) (fg : I.FG) : (m.map (algebraMap R (AdicCompletion I R
))).IsMaximal
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Ideal.fg_of_isNoetherianRing`：Ideal.fg_of_isNoetherianRing {R : Type*} [
Semiring R] [IsNoetherianRing R] (I : Ideal R) : I.FG
-/
lemma maximalIdeal_eq_map [IsNoetherianRing R] [IsLocalRing R] :
    maximalIdeal (AdicCompletion (maximalIdeal R) R) =
    (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ (le_refl _)
    (maximalIdeal R).fg_of_isNoetherianRing)).symm
/-
**AdicCompletion.mem_maximalIdeal_iff_eval_one_eq_zero** 是 Mathlib 中的一个引理，位于命名空间
 `AdicCompletion`。
形式化陈述：mem_maximalIdeal_iff_eval_one_eq_zero [IsNoetherianRing R] [IsLocalRing R]
 (x : AdicCompletion (maximalIdeal R) R) : x in maximalIdeal (AdicCompletion (ma
ximalIdeal R) R) ↔ x.1 1 = 0
参数：x : AdicCompletion (maximalIdeal R) R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AdicCompletion.pow_smul_top_eq_ker_eval`：pow_smul_top_eq_ker_eval {n : N
at} (h : I.FG) : I ^ n • ⊤ = (eval I M n).ker
· 使用引理 `Ideal.fg_of_isNoetherianRing`：Ideal.fg_of_isNoetherianRing {R : Type*} [
Semiring R] [IsNoetherianRing R] (I : Ideal R) : I.FG
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Ideal.smul_top_eq_map`：smul_top_eq_map {R S : Type*} [CommSemiring R] [C
ommSemiring S] [Algebra R S] (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (a
lgebraMap R…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AdicCompletion.instIsLocalRingMaximalIdealOfIsNoetherianRing`：∀ {R : Typ
e u_1} [inst : CommRing R] [IsNoetherianRing R] [inst_2 : IsLocalRing R],   IsLo
calRing (AdicCompletion (IsLocalRing.maximalIdeal …
· 使用引理 `AdicCompletion.maximalIdeal_eq_map`：maximalIdeal_eq_map [IsNoetherianRin
g R] [IsLocalRing R] : maximalIdeal (AdicCompletion (maximalIdeal R) R) = (maxim
alIdeal R).map (algebraM…
· 使用定理 `Submodule.restrictScalars_mem`：restrictScalars_mem (V : Submodule R M) (
m : M) : m in V.restrictScalars S ↔ m in V
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_maximalIdeal_iff_eval_one_eq_zero [IsNoetherianRing R] [IsLocalRing R]
    (x : AdicCompletion (maximalIdeal R) R) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) ↔ x.1 1 = 0 := by
  have : (AdicCompletion.eval (maximalIdeal R) R 1).ker =
    (maximalIdeal R) • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) := by
    simp [← pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing]
  rw [maximalIdeal_eq_map, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map]
  simp [← this, eval]
/-
**AdicCompletion.algebraMap_isLocalHom_of_fg** 是 Mathlib 中的一个引理，位于命名空间 `AdicComp
letion`。
形式化陈述：algebraMap_isLocalHom_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) : I
sLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R))
参数：fg : (maximalIdeal R).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AdicCompletion.isLocalRing_of_fg`：isLocalRing_of_fg [IsLocalRing R] (fg 
: (maximalIdeal R).FG) : IsLocalRing (AdicCompletion (maximalIdeal R) R)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsLocalRing.local_hom_TFAE`：local_hom_TFAE (f : R ->+* S) : List.TFAE [I
sLocalHom f, f '' maximalIdeal R subseteq maximalIdeal S, (maximalIdeal R).map f
 <= maximalIdeal…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AdicCompletion.maximalIdeal_eq_map_of_fg`：maximalIdeal_eq_map_of_fg [IsL
ocalRing R] (fg : (maximalIdeal R).FG) : haveI
-/
lemma algebraMap_isLocalHom_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    IsLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  have := AdicCompletion.isLocalRing_of_fg fg
  apply ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr
  simp [AdicCompletion.maximalIdeal_eq_map_of_fg fg]
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsNoetherianRing R] [IsLocalRing R] :
    IsLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  AdicCompletion.algebraMap_isLocalHom_of_fg (maximalIdeal R).fg_of_isNoetherianRing
/-
**AdicCompletion.isAdicComplete_of_fg** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`
。
形式化陈述：isAdicComplete_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) : haveI
参数：fg : (maximalIdeal R).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AdicCompletion.isLocalRing_of_fg`：isLocalRing_of_fg [IsLocalRing R] (fg 
: (maximalIdeal R).FG) : IsLocalRing (AdicCompletion (maximalIdeal R) R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AdicCompletion.maximalIdeal_eq_map_of_fg`：maximalIdeal_eq_map_of_fg [IsL
ocalRing R] (fg : (maximalIdeal R).FG) : haveI
· 使用引理 `AdicCompletion.isAdicComplete_self`：isAdicComplete_self (fg : I.FG) : Is
AdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R)
-/
lemma isAdicComplete_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    haveI := AdicCompletion.isLocalRing_of_fg fg
    IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (AdicCompletion (maximalIdeal R) R) := by
  rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg]
  exact AdicCompletion.isAdicComplete_self _ fg
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsNoetherianRing R] [IsLocalRing R] : IsAdicComplete
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)) (AdicCompletion (maximalIdeal R) R) :=
  AdicCompletion.isAdicComplete_of_fg (maximalIdeal R).fg_of_isNoetherianRing
/-
**AdicCompletion.residueField_map_bijective_of_fg** 是 Mathlib 中的一个引理，位于命名空间 `Adi
cCompletion`。
形式化陈述：residueField_map_bijective_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG
) : haveI
参数：fg : (maximalIdeal R).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AdicCompletion.isLocalRing_of_fg`：isLocalRing_of_fg [IsLocalRing R] (fg 
: (maximalIdeal R).FG) : IsLocalRing (AdicCompletion (maximalIdeal R) R)
· 使用引理 `AdicCompletion.algebraMap_isLocalHom_of_fg`：algebraMap_isLocalHom_of_fg 
[IsLocalRing R] (fg : (maximalIdeal R).FG) : IsLocalHom (algebraMap R (AdicCompl
etion (maximalIdeal R) R))
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `IsLocalRing.residue_surjective`：residue_surjective : Function.Surjective
 (IsLocalRing.residue R)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalRing.ResidueField.map_residue`：map_residue (f : R ->+* S) [IsLoca
lHom f] (r : R) : ResidueField.map f (residue R r) = residue S (f r)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.mk_eq_mk_iff_sub_mem`：mk_eq_mk_iff_sub_mem (x y : R) : mk
 I x = mk I y ↔ x - y in I
· 使用引理 `AdicCompletion.maximalIdeal_eq_map_of_fg`：maximalIdeal_eq_map_of_fg [IsL
ocalRing R] (fg : (maximalIdeal R).FG) : haveI
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.restrictScalars_mem`：restrictScalars_mem (V : Submodule R M) (
m : M) : m in V.restrictScalars S ↔ m in V
· 使用定理 `Ideal.smul_top_eq_map`：smul_top_eq_map {R S : Type*} [CommSemiring R] [C
ommSemiring S] [Algebra R S] (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (a
lgebraMap R…
· 使用定理 `AdicCompletion.algebraMap_apply`：algebraMap_apply [Algebra S R] (s : S) 
: algebraMap S (AdicCompletion I R) s = of I R (algebraMap S R s)
· 使用定理 `AdicCompletion.pow_smul_top_eq_ker_eval`：pow_smul_top_eq_ker_eval {n : N
at} (h : I.FG) : I ^ n • ⊤ = (eval I M n).ker
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
lemma residueField_map_bijective_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    haveI := AdicCompletion.isLocalRing_of_fg fg
    haveI := AdicCompletion.algebraMap_isLocalHom_of_fg fg
    Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
  have := AdicCompletion.isLocalRing_of_fg fg
  refine ⟨RingHom.injective _, fun x ↦ ?_⟩
  rcases residue_surjective x with ⟨y, hy⟩
  rcases Ideal.Quotient.mk_surjective (y.1 1) with ⟨z, hz⟩
  use residue R z
  rw [IsLocalRing.ResidueField.map_residue, ← hy]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [maximalIdeal_eq_map_of_fg fg, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map]
  have : (algebraMap R (AdicCompletion (maximalIdeal R) R)) z - y ∈
    (maximalIdeal R) ^ 1 • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) := by
    rw [AdicCompletion.algebraMap_apply, pow_smul_top_eq_ker_eval fg]
    simpa [eval, sub_eq_zero] using hz
  simpa

variable (R) in
/-
**AdicCompletion.residueField_map_bijective** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompl
etion`。
形式化陈述：residueField_map_bijective [IsNoetherianRing R] [IsLocalRing R] : Function
.Bijective (IsLocalRing.ResidueField.map (algebraMap R (AdicCompletion (maximalI
deal R) R)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AdicCompletion.residueField_map_bijective_of_fg`：residueField_map_biject
ive_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) : haveI
· 使用引理 `Ideal.fg_of_isNoetherianRing`：Ideal.fg_of_isNoetherianRing {R : Type*} [
Semiring R] [IsNoetherianRing R] (I : Ideal R) : I.FG
-/
lemma residueField_map_bijective [IsNoetherianRing R] [IsLocalRing R] :
    Function.Bijective (IsLocalRing.ResidueField.map
      (algebraMap R (AdicCompletion (maximalIdeal R) R))) :=
    AdicCompletion.residueField_map_bijective_of_fg (maximalIdeal R).fg_of_isNoetherianRing
/-
**AdicCompletion.spanFinrank_maximalIdeal_eq** 是 Mathlib 中的一个引理，位于命名空间 `AdicComp
letion`。
形式化陈述：spanFinrank_maximalIdeal_eq [IsNoetherianRing R] [IsLocalRing R] : (maxima
lIdeal (AdicCompletion (maximalIdeal R) R)).spanFinrank = (maximalIdeal R).spanF
inrank
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.fg_of_isNoetherianRing`：Ideal.fg_of_isNoetherianRing {R : Type*} [
Semiring R] [IsNoetherianRing R] (I : Ideal R) : I.FG
· 使用定理 `AdicCompletion.instIsLocalRingMaximalIdealOfIsNoetherianRing`：∀ {R : Typ
e u_1} [inst : CommRing R] [IsNoetherianRing R] [inst_2 : IsLocalRing R],   IsLo
calRing (AdicCompletion (IsLocalRing.maximalIdeal …
· 使用引理 `IsLocalRing.maximalIdeal_comap`：maximalIdeal_comap (f : R ->+* S) [IsLoc
alHom f] : (maximalIdeal S).comap f = maximalIdeal R
· 使用定理 `AdicCompletion.instIsLocalHomMaximalIdealRingHomAlgebraMapOfIsNoetherian
Ring`：∀ {R : Type u_1} [inst : CommRing R] [IsNoetherianRing R] [inst_2 : IsLoca
lRing R],   IsLocalHom (algebraMap R (AdicCompletion (IsLocalRing.…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LinearMap.ker_eq_bot'`：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ fo
rall m, f m = 0 -> m = 0
· 使用定理 `Ideal.toCotangent_surjective`：toCotangent_surjective : Function.Surjecti
ve I.toCotangent
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `AdicCompletion.pow_smul_top_eq_ker_eval`：pow_smul_top_eq_ker_eval {n : N
at} (h : I.FG) : I ^ n • ⊤ = (eval I M n).ker
· 使用定理 `Ideal.smul_top_eq_map`：smul_top_eq_map {R S : Type*} [CommSemiring R] [C
ommSemiring S] [Algebra R S] (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (a
lgebraMap R…
· 使用定理 `Submodule.restrictScalars_mem`：restrictScalars_mem (V : Submodule R M) (
m : M) : m in V.restrictScalars S ↔ m in V
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `AdicCompletion.maximalIdeal_eq_map`：maximalIdeal_eq_map [IsNoetherianRin
g R] [IsLocalRing R] : maximalIdeal (AdicCompletion (maximalIdeal R) R) = (maxim
alIdeal R).map (algebraM…
· 使用定理 `Submodule.Quotient.mk_surjective`：mk_surjective : Function.Surjective (@
mk _ _ _ _ _ p)
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AdicCompletion.mem_maximalIdeal_iff_eval_one_eq_zero`：mem_maximalIdeal_i
ff_eval_one_eq_zero [IsNoetherianRing R] [IsLocalRing R] (x : AdicCompletion (ma
ximalIdeal R) R) : x in maximalIdeal (Adic…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `rank_eq_of_equiv_equiv`：rank_eq_of_equiv_equiv (i : R -> R') (j : M ≃+ M
₁) (hi : Bijective i) (hc : forall (r : R) (m : M), j (r • m) = i r • j m) : Mod
ule.rank R M…
· 使用引理 `AdicCompletion.residueField_map_bijective`：residueField_map_bijective [I
sNoetherianRing R] [IsLocalRing R] : Function.Bijective (IsLocalRing.ResidueFiel
d.map (algebraMap R (AdicComple…
· 使用引理 `IsLocalRing.residue_surjective`：residue_surjective : Function.Surjective
 (IsLocalRing.residue R)
（共 37 条，此处仅展示前 30 条）
-/
lemma spanFinrank_maximalIdeal_eq [IsNoetherianRing R] [IsLocalRing R] :
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)).spanFinrank =
    (maximalIdeal R).spanFinrank := by
  have fg : (maximalIdeal R).FG := fg_of_isNoetherianRing (maximalIdeal R)
  have comapeq := IsLocalRing.maximalIdeal_comap (algebraMap R (AdicCompletion (maximalIdeal R) R))
  let f := Ideal.mapCotangent _ _ (Algebra.ofId R (AdicCompletion (maximalIdeal R) R))
    (le_of_eq comapeq.symm)
  have inj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    rcases Ideal.toCotangent_surjective _ m with ⟨m', hm'⟩
    simp only [← hm', mapCotangent_toCotangent, Algebra.ofId_apply, toCotangent_eq_zero,
      maximalIdeal_eq_map, ← Ideal.map_pow, f] at hm
    rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
      pow_smul_top_eq_ker_eval fg] at hm
    have : (algebraMap R (AdicCompletion (maximalIdeal R) R)) m'.1 = of _ R m'.1 := rfl
    simp only [smul_eq_mul, eval, this, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk,
      of_apply, Submodule.mkQ_apply, mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hm
    simpa [← hm', toCotangent_eq_zero] using hm
  have surj : Function.Surjective f := by
    intro m
    rcases Ideal.toCotangent_surjective _ m with ⟨m', hm'⟩
    rcases Submodule.Quotient.mk_surjective _ (m'.1.1 2) with ⟨l, hl⟩
    have lmem : (transitionMap _ R (Nat.le_succ 1)) (m'.1.1 2) = m'.1.1 1 := m'.1.2 (Nat.le_succ 1)
    simp only [smul_eq_mul, Nat.succ_eq_add_one, Nat.reduceAdd, transitionMap, Submodule.factorPow,
      Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, ← hl, mk_eq_mk, factor_mk, pow_one,
      (mem_maximalIdeal_iff_eval_one_eq_zero m'.1).mp m'.2, eq_zero_iff_mem, mul_top] at lmem
    use (maximalIdeal R).toCotangent ⟨l, lmem⟩
    simp only [mapCotangent_toCotangent, Algebra.ofId_apply, ← hm', toCotangent_eq, f]
    change (of (maximalIdeal R) R l) - m' ∈ _
    simp only [maximalIdeal_eq_map, ← Ideal.map_pow]
    rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map]
    simpa [pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing, eval, sub_eq_zero]
      using hl
  have rkeq := rank_eq_of_equiv_equiv _
    (LinearEquiv.ofBijective f ⟨inj, surj⟩).toAddEquiv
    (residueField_map_bijective R) (fun r m ↦ by
      rcases IsLocalRing.residue_surjective r with ⟨s, rfl⟩
      exact map_smul f s m )
  have fg' : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).FG := by
    simpa [AdicCompletion.maximalIdeal_eq_map] using fg.map _
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg fg,
    IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg fg', eq_comm]
  simp [Module.finrank, CotangentSpace, rkeq]

end AdicCompletion

