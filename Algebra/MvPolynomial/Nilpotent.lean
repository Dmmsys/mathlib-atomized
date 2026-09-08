/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Nilpotents and units in multivariate polynomial rings

We prove that
- `MvPolynomial.isNilpotent_iff`:
  A multivariate polynomial is nilpotent iff all its coefficients are.
- `MvPolynomial.isUnit_iff`:
  A multivariate polynomial is invertible iff its constant term is invertible
  and its other coefficients are nilpotent.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] {P : MvPolynomial σ R}

-- Subsumed by `isNilpotent_iff` below.
/-
**MvPolynomial.isNilpotent_iff_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem isNilpotent_iff_of_fintype [Finite σ] :
    IsNilpotent P ↔ ∀ i, IsNilpotent (P.coeff i) := by
  classical
  -- Note: including `Fintype.ofFinite σ` in the entire context interferes with the `rw` below.
  refine have := Fintype.ofFinite σ; Fintype.induction_empty_option ?_ ?_ ?_ σ P
  · intro α β _ e h₁ P
    rw [← IsNilpotent.map_iff (rename_injective _ e.symm.injective), h₁,
      (Finsupp.equivCongrLeft e).forall_congr_left]
    simp [Finsupp.equivMapDomain_eq_mapDomain, coeff_rename_mapDomain _ e.symm.injective]
  · simp [Unique.forall_iff, ← IsNilpotent.map_iff (isEmptyRingEquiv R PEmpty).injective,
      -isEmptyRingEquiv_apply, isEmptyRingEquiv_eq_coeff_zero]
  · intro α _ H P
    obtain ⟨P, rfl⟩ := (optionEquivLeft _ _).symm.surjective P
    simp [IsNilpotent.map_iff (optionEquivLeft _ _).symm.injective,
      Polynomial.isNilpotent_iff, H, Finsupp.optionEquiv.forall_congr_left,
      ← optionEquivLeft_coeff_some_coeff_none, Finsupp.coe_update]
/-
**MvPolynomial.isNilpotent_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：isNilpotent_iff : IsNilpotent P ↔ forall i, IsNilpotent (P.coeff i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.exists_fin_rename`：exists_fin_rename (p : MvPolynomial σ R)
 : exists (n : Nat) (f : Fin n -> σ) (_hf : Injective f) (q : MvPolynomial (Fin 
n) R), p = rename f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsNilpotent.map_iff`：IsNilpotent.map_iff [MonoidWithZero R] [MonoidWithZ
ero S] {r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] {f : F
} (hf : F…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MvPolynomial.rename_injective`：rename_injective (f : σ -> τ) (hf : Funct
ion.Injective f) : Function.Injective (rename f : MvPolynomial σ R -> MvPolynomi
al τ R)
· 使用定理 `_private.Mathlib.Algebra.MvPolynomial.Nilpotent.0.MvPolynomial.isNilpote
nt_iff_of_fintype`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommRing R] {P : MvPo
lynomial σ R} [Finite σ],   IsNilpotent P ↔ ∀ (i : σ →₀ ℕ), IsNilpotent (MvPoly…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Function.instCanLiftForallEmbeddingCoeInjective`：∀ {α : Sort u_1} {β : S
ort u_2}, CanLift (α → β) (α ↪ β) DFunLike.coe Function.Injective
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.coeff_rename_embDomain`：coeff_rename_embDomain (f : σ ↪ τ) 
(φ : MvPolynomial σ R) (d : σ ->₀ Nat) : (rename f φ).coeff (d.embDomain f) = φ.
coeff d
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MvPolynomial.coeff_rename_eq_zero`：coeff_rename_eq_zero (f : σ -> τ) (φ 
: MvPolynomial σ R) (d : τ ->₀ Nat) (h : forall u : σ ->₀ Nat, u.mapDomain f = d
 -> φ.coeff u = 0) : (r…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.embDomain_eq_mapDomain`：embDomain_eq_mapDomain (f : α ↪ β) (v : 
α ->₀ M) : embDomain f v = mapDomain f v
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isNilpotent_iff : IsNilpotent P ↔ ∀ i, IsNilpotent (P.coeff i) := by
  obtain ⟨n, f, hf, P, rfl⟩ := P.exists_fin_rename
  rw [IsNilpotent.map_iff (rename_injective _ hf), MvPolynomial.isNilpotent_iff_of_fintype]
  lift f to Fin n ↪ σ using hf
  refine ⟨fun H i ↦ ?_, fun H i ↦ by simpa using H (i.embDomain f)⟩
  by_cases H : i ∈ Set.range (Finsupp.embDomain f)
  · aesop
  · rw [coeff_rename_eq_zero] <;> aesop (add simp Finsupp.embDomain_eq_mapDomain)
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsReduced R] : IsReduced (MvPolynomial σ R) := by
  simp [isReduced_iff, isNilpotent_iff, MvPolynomial.ext_iff]
/-
**MvPolynomial.isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：isUnit_iff : IsUnit P ↔ IsUnit (P.coeff 0) ∧ forall i != 0, IsNilpotent (P
.coeff i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.coeff_isUnit_isNilpotent_of_isUnit`：coeff_isUnit_isNilpotent_
of_isUnit (hunit : IsUnit P) : IsUnit (P.coeff 0) ∧ (forall i, i != 0 -> IsNilpo
tent (P.coeff i))
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.optionEquivLeft_coeff_some_coeff_none`：optionEquivLeft_coef
f_some_coeff_none (n : Option S₁ ->₀ Nat) (f : MvPolynomial (Option S₁) R) : coe
ff n.some (Polynomial.coeff (optionEquiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.equivMapDomain_eq_mapDomain`：equivMapDomain_eq_mapDomain {M} [Ad
dCommMonoid M] (f : α ≃ β) (l : α ->₀ M) : equivMapDomain f l = mapDomain f l
· 使用定理 `MvPolynomial.renameEquiv_apply`：∀ {σ : Type u_1} {τ : Type u_2} (R : Typ
e u_4) [inst : CommSemiring R] (f : σ ≃ τ) (a : MvPolynomial σ R),   (MvPolynomi
al.renameEquiv R f) …
· 使用定理 `MvPolynomial.coeff_rename_mapDomain`：coeff_rename_mapDomain (f : σ -> τ)
 (hf : Injective f) (φ : MvPolynomial σ R) (d : σ ->₀ Nat) : (rename f φ).coeff 
(d.mapDomain f) = φ.coeff…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MvPolynomial.coeff_sub`：coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p - q) = coeff m p - coeff m q
· 使用定理 `MvPolynomial.coeff_C`：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : M
vPolynomial σ R) = if 0 = m then a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
（共 37 条，此处仅展示前 30 条）
-/
theorem isUnit_iff : IsUnit P ↔ IsUnit (P.coeff 0) ∧ ∀ i ≠ 0, IsNilpotent (P.coeff i) := by
  classical
  refine ⟨fun H ↦ ⟨H.map constantCoeff, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · intro n hn
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by simpa [Finsupp.ext_iff] using hn
    let e := (optionEquivLeft _ _).symm.trans (renameEquiv R (Equiv.optionSubtypeNe i))
    have H := (Polynomial.coeff_isUnit_isNilpotent_of_isUnit (H.map e.symm)).2 (n i) hi
    simp only [ne_eq, isNilpotent_iff] at H
    convert! ← H (n.equivMapDomain (Equiv.optionSubtypeNe i).symm).some
    refine (optionEquivLeft_coeff_some_coeff_none _ _ _ _).trans ?_
    simp [Finsupp.equivMapDomain_eq_mapDomain,
      coeff_rename_mapDomain _ (Equiv.optionSubtypeNe i).symm.injective]
  · have : IsNilpotent (P - C (P.coeff 0)) := by
      simp +contextual [isNilpotent_iff, apply_ite, eq_comm, h₂]
    simpa using this.isUnit_add_right_of_commute (h₁.map C) (.all _ _)
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalHom (C : _ →+* MvPolynomial σ R) where
  map_nonunit := by simp +contextual [isUnit_iff]
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalHom (algebraMap R (MvPolynomial σ R)) :=
  inferInstanceAs (IsLocalHom C)
/-
**MvPolynomial.isUnit_iff_totalDegree_of_isReduced** 是 Mathlib 中的一个定理，位于命名空间 `Mv
Polynomial`。
形式化陈述：isUnit_iff_totalDegree_of_isReduced [IsReduced R] : IsUnit P ↔ IsUnit (P.c
oeff 0) ∧ P.totalDegree = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.totalDegree_eq_zero_iff`：totalDegree_eq_zero_iff (p : MvPol
ynomial σ R) : p.totalDegree = 0 ↔ forall (m : σ ->₀ Nat) (_ : m in p.support) (
x : σ), m x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MvPolynomial.isUnit_iff`：isUnit_iff : IsUnit P ↔ IsUnit (P.coeff 0) ∧ fo
rall i != 0, IsNilpotent (P.coeff i)
-/
theorem isUnit_iff_totalDegree_of_isReduced [IsReduced R] :
    IsUnit P ↔ IsUnit (P.coeff 0) ∧ P.totalDegree = 0 := by
  convert! isUnit_iff (P := P)
  rw [totalDegree_eq_zero_iff]
  simp [not_imp_comm (a := _ = (0 : R)), Finsupp.ext_iff]
/-
**MvPolynomial.isUnit_iff_eq_C_of_isReduced** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynom
ial`。
形式化陈述：isUnit_iff_eq_C_of_isReduced [IsReduced R] : IsUnit P ↔ exists r, IsUnit r
 ∧ P = C r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.isUnit_iff_totalDegree_of_isReduced`：isUnit_iff_totalDegree
_of_isReduced [IsReduced R] : IsUnit P ↔ IsUnit (P.coeff 0) ∧ P.totalDegree = 0
· 使用定理 `MvPolynomial.totalDegree_eq_zero_iff_eq_C`：totalDegree_eq_zero_iff_eq_C 
{p : MvPolynomial σ R} : p.totalDegree = 0 ↔ p = C (p.coeff 0)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.coeff_zero_C`：coeff_zero_C (a) : coeff 0 (C a : MvPolynomia
l σ R) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isUnit_iff_eq_C_of_isReduced [IsReduced R] :
    IsUnit P ↔ ∃ r, IsUnit r ∧ P = C r := by
  rw [isUnit_iff_totalDegree_of_isReduced, totalDegree_eq_zero_iff_eq_C]
  refine ⟨fun H ↦ ⟨_, H⟩, ?_⟩
  rintro ⟨r, hr, rfl⟩
  simpa

end MvPolynomial

