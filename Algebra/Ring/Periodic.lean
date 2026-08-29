/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
module

public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Periodicity

In this file we define and then prove facts about periodic and antiperiodic functions.

## Main definitions

* `Function.Periodic`: A function `f` is *periodic* if `∀ x, f (x + c) = f x`.
  `f` is referred to as periodic with period `c` or `c`-periodic.

* `Function.Antiperiodic`: A function `f` is *antiperiodic* if `∀ x, f (x + c) = -f x`.
  `f` is referred to as antiperiodic with antiperiod `c` or `c`-antiperiodic.

Note that any `c`-antiperiodic function will necessarily also be `2 • c`-periodic.

## Tags

period, periodic, periodicity, antiperiodic
-/

@[expose] public section

assert_not_exists Field

variable {α β γ : Type*} {f g : α -> β} {c c₁ c₂ x : α}

open Set

namespace Function

/-! ### Periodicity -/


/-- A function `f` is said to be `Periodic` with period `c` if for all `x`, `f (x + c) = f x`. -/
@[simp, wikidata Q184743]
/--
Definition of `Periodic` / `Periodic` 的定义

English:
definition Periodic
  signature: [Add α] (f : α -> β) (c : α)
  body: forall x : α, f (x + c) = f x

中文:
定义 周期
  签名: [加法 α] (f : α -> β) (c : α)
  定义体: forall x : α, f (x + c) = f x

Depends on / 依赖: Nonempty, Subsingleton
-/
def Periodic [Add α] (f : α -> β) (c : α) : Prop :=
  forall x : α, f (x + c) = f x

/--
theorem `Periodic.funext` / 定理 `Periodic.funext`

English:
theorem Periodic.funext
  given: [Add α] (h : Periodic f c)
  statement: (fun x => f (x + c)) = f
  proof: funext h

中文:
定理 周期.funext
  条件: [加法 α] (h : 周期 f c)
  结论: (fun x => f (x + c)) = f
  证明: funext h
-/
protected theorem Periodic.funext [Add α] (h : Periodic f c) : (fun x => f (x + c)) = f :=
  funext h

/--
theorem `Periodic.comp` / 定理 `Periodic.comp`

English:
theorem Periodic.comp
  given: [Add α] (h : Periodic f c) (g : β -> γ)
  statement: Periodic (g ∘ f) c
  proof: by
  simp_all

中文:
定理 周期.comp
  条件: [加法 α] (h : 周期 f c) (g : β -> γ)
  结论: 周期 (g ∘ f) c
  证明: by
  simp_all
-/
protected theorem Periodic.comp [Add α] (h : Periodic f c) (g : β -> γ) : Periodic (g ∘ f) c := by
  simp_all

/--
theorem `Periodic.comp_addHom` / 定理 `Periodic.comp_addHom`

English:
theorem Periodic.comp_addHom
  statement: [Add α] [Add γ] (h : Periodic f c) (g : AddHom γ α) (g_inv : α -> γ)
  proof: fun x => by
  simp only [hg c, h (g x), map_add, comp_apply]

@[to_additive]

中文:
定理 周期.comp_addHom
  结论: [加法 α] [加法 γ] (h : 周期 f c) (g : 加法半群态射 γ α) (g_inv : α -> γ)
  证明: fun x => by
  simp only [hg c, h (g x), map_add, comp_apply]

@[to_additive]

Depends on / 依赖: comp_apply, map_add
-/
theorem Periodic.comp_addHom [Add α] [Add γ] (h : Periodic f c) (g : AddHom γ α) (g_inv : α -> γ)
    (hg : RightInverse g_inv g) : Periodic (f ∘ g) (g_inv c) := fun x => by
  simp only [hg c, h (g x), map_add, comp_apply]

@[to_additive]
/--
theorem `Periodic.mul` / 定理 `Periodic.mul`

English:
theorem Periodic.mul
  given: [Add α] [Mul β] (hf : Periodic f c) (hg : Periodic g c)
  proof: by simp_all

@[to_additive]

中文:
定理 周期.mul
  条件: [加法 α] [乘法 β] (hf : 周期 f c) (hg : 周期 g c)
  证明: by simp_all

@[to_additive]
-/
protected theorem Periodic.mul [Add α] [Mul β] (hf : Periodic f c) (hg : Periodic g c) :
    Periodic (f * g) c := by simp_all

@[to_additive]
/--
theorem `Periodic.div` / 定理 `Periodic.div`

English:
theorem Periodic.div
  given: [Add α] [Div β] (hf : Periodic f c) (hg : Periodic g c)
  proof: by simp_all

@[to_additive]

中文:
定理 周期.div
  条件: [加法 α] [除法 β] (hf : 周期 f c) (hg : 周期 g c)
  证明: by simp_all

@[to_additive]
-/
protected theorem Periodic.div [Add α] [Div β] (hf : Periodic f c) (hg : Periodic g c) :
    Periodic (f / g) c := by simp_all

@[to_additive]
/--
theorem `_root_.List.periodic_prod` / 定理 `_root_.List.periodic_prod`

English:
theorem _root_.List.periodic_prod
  statement: [Add α] [MulOneClass β] (l : List (α -> β))
  proof: by
  induction l with
  | nil => simp
  | cons g l ih =>
    rw [List.forall_mem_cons] at hl
    simpa only [List.prod_cons] using hl.1.mul (ih hl.2)

@[to_additive]

中文:
定理 _root_.列表.periodic_prod
  结论: [加法 α] [MulOne类 β] (l : 列表 (α -> β))
  证明: by
  induction l with
  | nil => simp
  | cons g l ih =>
    rw [List.forall_mem_cons] at hl
    simpa only [List.prod_cons] using hl.1.mul (ih hl.2)

@[to_additive]

Depends on / 依赖: List.forall_mem_cons, List.prod_cons, forall_mem_cons, prod_cons
-/
theorem _root_.List.periodic_prod [Add α] [MulOneClass β] (l : List (α -> β))
    (hl : forall f in l, Periodic f c) : Periodic l.prod c := by
  induction l with
  | nil => simp
  | cons g l ih =>
    rw [List.forall_mem_cons] at hl
    simpa only [List.prod_cons] using hl.1.mul (ih hl.2)

@[to_additive]
/--
theorem `_root_.Multiset.periodic_prod` / 定理 `_root_.Multiset.periodic_prod`

English:
theorem _root_.Multiset.periodic_prod
  statement: [Add α] [CommMonoid β] (s : Multiset (α -> β))
  proof: (s.prod_toList ▸ s.toList.periodic_prod) fun f hf => hs f Multiset.mem_toList.mp hf

@[to_additive]

中文:
定理 _root_.Multiset.periodic_prod
  结论: [加法 α] [交换幺半群 β] (s : Multiset (α -> β))
  证明: (s.prod_toList ▸ s.toList.periodic_prod) fun f hf => hs f Multiset.mem_toList.mp hf

@[to_additive]

Depends on / 依赖: Multiset, Multiset.mem_toList.mp, mem_toList, periodic_prod, prod_toList, s.prod_toList, s.toList.periodic_prod, toList
-/
theorem _root_.Multiset.periodic_prod [Add α] [CommMonoid β] (s : Multiset (α -> β))
    (hs : forall f in s, Periodic f c) : Periodic s.prod c :=
(s.prod_toList ▸ s.toList.periodic_prod) fun f hf => hs f Multiset.mem_toList.mp hf

@[to_additive]
/--
theorem `_root_.Finset.periodic_prod` / 定理 `_root_.Finset.periodic_prod`

English:
theorem _root_.Finset.periodic_prod
  statement: [Add α] [CommMonoid β] {ι : Type*} {f : ι -> α -> β}
  proof: s.prod_map_toList f ▸ (s.toList.map f).periodic_prod (by simpa [-Periodic])

@[to_additive]

中文:
定理 _root_.有限集.periodic_prod
  结论: [加法 α] [交换幺半群 β] {ι : 类型} {f : ι -> α -> β}
  证明: s.prod_map_toList f ▸ (s.toList.map f).periodic_prod (by simpa [-Periodic])

@[to_additive]

Depends on / 依赖: CategoryTheory, CategoryTheory.epi_comp_iff_of_isIso, CategoryTheory.forget, Limits, Periodic, Scheme, Scheme.pullbackComparison_forget_surjective, TopCat, _root_, _root_.CategoryTheory.Limits.pullbackComparison_comp, epi_comp_iff_of_isIso, epi_iff_surjective, epi_of_epi_map, forget, forgetToTop, forgetToTop.map, periodic_prod, prod_map_toList, pullbackComparison, pullbackComparison_comp
-/
theorem _root_.Finset.periodic_prod [Add α] [CommMonoid β] {ι : Type*} {f : ι -> α -> β}
    (s : Finset ι) (hs : forall i in s, Periodic (f i) c) : Periodic (∏ i in s, f i) c :=
  s.prod_map_toList f ▸ (s.toList.map f).periodic_prod (by simpa [-Periodic])

@[to_additive]
/--
theorem `Periodic.smul` / 定理 `Periodic.smul`

English:
theorem Periodic.smul
  given: [Add α] [SMul γ β] (h : Periodic f c) (a : γ)
  proof: by simp_all

中文:
定理 周期.smul
  条件: [加法 α] [标量乘法 γ β] (h : 周期 f c) (a : γ)
  证明: by simp_all
-/
protected theorem Periodic.smul [Add α] [SMul γ β] (h : Periodic f c) (a : γ) :
    Periodic (a • f) c := by simp_all

/--
theorem `Periodic.const_smul` / 定理 `Periodic.const_smul`

English:
theorem Periodic.const_smul
  statement: [AddMonoid α] [Group γ] [DistribMulAction γ α]
  proof: fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)

中文:
定理 周期.const_smul
  结论: [加法幺半群 α] [群 γ] [分配乘法作用 γ α]
  证明: fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)
-/
protected theorem Periodic.const_smul [AddMonoid α] [Group γ] [DistribMulAction γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)

/--
theorem `Periodic.const_inv_smul` / 定理 `Periodic.const_inv_smul`

English:
theorem Periodic.const_inv_smul
  statement: [AddMonoid α] [Group γ] [DistribMulAction γ α] (h : Periodic f c)
  proof: by
  simpa only [inv_inv] using h.const_smul a⁻¹

中文:
定理 周期.const_inv_smul
  结论: [加法幺半群 α] [群 γ] [分配乘法作用 γ α] (h : 周期 f c)
  证明: by
  simpa only [inv_inv] using h.const_smul a⁻¹

Depends on / 依赖: const_smul, h.const_smul, inv_inv
-/
theorem Periodic.const_inv_smul [AddMonoid α] [Group γ] [DistribMulAction γ α] (h : Periodic f c)
    (a : γ) : Periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul a⁻¹

/--
theorem `Periodic.add_period` / 定理 `Periodic.add_period`

English:
theorem Periodic.add_period
  given: [AddSemigroup α] (h1 : Periodic f c₁) (h2 : Periodic f c₂)
  proof: by simp_all [← add_assoc]

中文:
定理 周期.add_period
  条件: [加法半群 α] (h1 : 周期 f c₁) (h2 : 周期 f c₂)
  证明: by simp_all [← add_assoc]

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, add_assoc, pullback_fst
-/
theorem Periodic.add_period [AddSemigroup α] (h1 : Periodic f c₁) (h2 : Periodic f c₂) :
    Periodic f (c₁ + c₂) := by simp_all [← add_assoc]

/--
theorem `Periodic.sub_eq` / 定理 `Periodic.sub_eq`

English:
theorem Periodic.sub_eq
  given: [AddGroup α] (h : Periodic f c) (x : α)
  statement: f (x - c) = f x
  proof: by
  simpa only [sub_add_cancel] using (h (x - c)).symm

中文:
定理 周期.sub_eq
  条件: [加法群 α] (h : 周期 f c) (x : α)
  结论: f (x - c) = f x
  证明: by
  simpa only [sub_add_cancel] using (h (x - c)).symm

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd, sub_add_cancel
-/
theorem Periodic.sub_eq [AddGroup α] (h : Periodic f c) (x : α) : f (x - c) = f x := by
  simpa only [sub_add_cancel] using (h (x - c)).symm

/--
theorem `Periodic.sub_eq'` / 定理 `Periodic.sub_eq'`

English:
theorem Periodic.sub_eq'
  given: [SubtractionCommMonoid α] (h : Periodic f c)
  statement: f (c - x) = f (-x)
  proof: by
  simpa only [sub_eq_neg_add] using h (-x)

中文:
定理 周期.sub_eq'
  条件: [SubtractionComm幺半群 α] (h : 周期 f c)
  结论: f (c - x) = f (-x)
  证明: by
  simpa only [sub_eq_neg_add] using h (-x)

Depends on / 依赖: sub_eq_neg_add
-/
theorem Periodic.sub_eq' [SubtractionCommMonoid α] (h : Periodic f c) : f (c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h (-x)

/--
theorem `Periodic.neg` / 定理 `Periodic.neg`

English:
theorem Periodic.neg
  given: [AddGroup α] (h : Periodic f c)
  statement: Periodic f (-c)
  proof: by
  simpa only [sub_eq_add_neg, Periodic] using h.sub_eq

中文:
定理 周期.neg
  条件: [加法群 α] (h : 周期 f c)
  结论: 周期 f (-c)
  证明: by
  simpa only [sub_eq_add_neg, Periodic] using h.sub_eq
-/
protected theorem Periodic.neg [AddGroup α] (h : Periodic f c) : Periodic f (-c) := by
  simpa only [sub_eq_add_neg, Periodic] using h.sub_eq

/--
theorem `Periodic.sub_period` / 定理 `Periodic.sub_period`

English:
theorem Periodic.sub_period
  given: [AddGroup α] (h1 : Periodic f c₁) (h2 : Periodic f c₂)
  proof: fun x => by
  rw [sub_eq_add_neg]; rw [← add_assoc]; rw [h2.neg]; rw [h1]

中文:
定理 周期.sub_period
  条件: [加法群 α] (h1 : 周期 f c₁) (h2 : 周期 f c₂)
  证明: fun x => by
  rw [sub_eq_add_neg]; rw [← add_assoc]; rw [h2.neg]; rw [h1]

Depends on / 依赖: add_assoc, h2.neg, sub_eq_add_neg
-/
theorem Periodic.sub_period [AddGroup α] (h1 : Periodic f c₁) (h2 : Periodic f c₂) :
    Periodic f (c₁ - c₂) := fun x => by
  rw [sub_eq_add_neg]; rw [← add_assoc]; rw [h2.neg]; rw [h1]

/--
theorem `Periodic.const_add` / 定理 `Periodic.const_add`

English:
theorem Periodic.const_add
  given: [AddSemigroup α] (h : Periodic f c) (a : α)
  proof: fun x => by simpa [add_assoc] using h (a + x)

中文:
定理 周期.const_add
  条件: [加法半群 α] (h : 周期 f c) (a : α)
  证明: fun x => by simpa [add_assoc] using h (a + x)

Depends on / 依赖: add_assoc
-/
theorem Periodic.const_add [AddSemigroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a + x)) c := fun x => by simpa [add_assoc] using h (a + x)

/--
theorem `Periodic.add_const` / 定理 `Periodic.add_const`

English:
theorem Periodic.add_const
  given: [AddCommSemigroup α] (h : Periodic f c) (a : α)
  proof: fun x => by
  simpa only [add_right_comm] using h (x + a)

中文:
定理 周期.add_const
  条件: [加法交换半群 α] (h : 周期 f c) (a : α)
  证明: fun x => by
  simpa only [add_right_comm] using h (x + a)

Depends on / 依赖: add_right_comm
-/
theorem Periodic.add_const [AddCommSemigroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x + a)) c := fun x => by
  simpa only [add_right_comm] using h (x + a)

/--
theorem `Periodic.const_sub` / 定理 `Periodic.const_sub`

English:
theorem Periodic.const_sub
  given: [AddCommGroup α] (h : Periodic f c) (a : α)
  proof: fun x => by
  simp only [← sub_sub, h.sub_eq]

中文:
定理 周期.const_sub
  条件: [加法交换群 α] (h : 周期 f c) (a : α)
  证明: fun x => by
  simp only [← sub_sub, h.sub_eq]

Depends on / 依赖: h.sub_eq, sub_eq, sub_sub
-/
theorem Periodic.const_sub [AddCommGroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a - x)) c := fun x => by
  simp only [← sub_sub, h.sub_eq]

/--
theorem `Periodic.sub_const` / 定理 `Periodic.sub_const`

English:
theorem Periodic.sub_const
  given: [SubtractionCommMonoid α] (h : Periodic f c) (a : α)
  proof: by
  simpa only [sub_eq_add_neg] using h.add_const (-a)

中文:
定理 周期.sub_const
  条件: [SubtractionComm幺半群 α] (h : 周期 f c) (a : α)
  证明: by
  simpa only [sub_eq_add_neg] using h.add_const (-a)

Depends on / 依赖: add_const, h.add_const, sub_eq_add_neg
-/
theorem Periodic.sub_const [SubtractionCommMonoid α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x - a)) c := by
  simpa only [sub_eq_add_neg] using h.add_const (-a)

/--
theorem `Periodic.nsmul` / 定理 `Periodic.nsmul`

English:
theorem Periodic.nsmul
  given: [AddMonoid α] (h : Periodic f c) (n : Nat)
  statement: Periodic f (n • c)
  proof: by
  induction n <;> simp_all [add_nsmul, ← add_assoc]

中文:
定理 周期.nsmul
  条件: [加法幺半群 α] (h : 周期 f c) (n : 自然数)
  结论: 周期 f (n • c)
  证明: by
  induction n <;> simp_all [add_nsmul, ← add_assoc]

Depends on / 依赖: add_assoc, add_nsmul
-/
theorem Periodic.nsmul [AddMonoid α] (h : Periodic f c) (n : Nat) : Periodic f (n • c) := by
  induction n <;> simp_all [add_nsmul, ← add_assoc]

/--
theorem `Periodic.nat_mul` / 定理 `Periodic.nat_mul`

English:
theorem Periodic.nat_mul
  given: [NonAssocSemiring α] (h : Periodic f c) (n : Nat)
  statement: Periodic f (n * c)
  proof: by
  simpa only [nsmul_eq_mul] using h.nsmul n

中文:
定理 周期.nat_mul
  条件: [非结合半环 α] (h : 周期 f c) (n : 自然数)
  结论: 周期 f (n * c)
  证明: by
  simpa only [nsmul_eq_mul] using h.nsmul n

Depends on / 依赖: Category, Category.assoc, h.nsmul, lift_fst_assoc, nsmul_eq_mul, pullback, pullback.lift_fst_assoc, pullbackRightPullbackFstIso_hom_fst_assoc, pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullbackSymmetry_hom_comp_fst_assoc, t_fst_fst
-/
theorem Periodic.nat_mul [NonAssocSemiring α] (h : Periodic f c) (n : Nat) : Periodic f (n * c) := by
  simpa only [nsmul_eq_mul] using h.nsmul n

/--
theorem `Periodic.neg_nsmul` / 定理 `Periodic.neg_nsmul`

English:
theorem Periodic.neg_nsmul
  given: [AddGroup α] (h : Periodic f c) (n : Nat)
  statement: Periodic f (-(n • c))
  proof: (h.nsmul n).neg

中文:
定理 周期.neg_nsmul
  条件: [加法群 α] (h : 周期 f c) (n : 自然数)
  结论: 周期 f (-(n • c))
  证明: (h.nsmul n).neg

Depends on / 依赖: Category, Category.assoc, h.nsmul, lift_fst_assoc, pullback, pullback.lift_fst_assoc, pullbackRightPullbackFstIso_hom_fst_assoc, pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullbackSymmetry_hom_comp_fst_assoc, t_fst_snd
-/
theorem Periodic.neg_nsmul [AddGroup α] (h : Periodic f c) (n : Nat) : Periodic f (-(n • c)) :=
  (h.nsmul n).neg

/--
theorem `Periodic.neg_nat_mul` / 定理 `Periodic.neg_nat_mul`

English:
theorem Periodic.neg_nat_mul
  given: [NonAssocRing α] (h : Periodic f c) (n : Nat)
  statement: Periodic f (-(n * c))
  proof: (h.nat_mul n).neg

中文:
定理 周期.neg_nat_mul
  条件: [非结合环 α] (h : 周期 f c) (n : 自然数)
  结论: 周期 f (-(n * c))
  证明: (h.nat_mul n).neg

Depends on / 依赖: Category, Category.assoc, Category.comp_id, comp_id, h.nat_mul, lift_snd, nat_mul, pullback, pullback.lift_snd, pullbackRightPullbackFstIso_hom_snd, pullbackRightPullbackFstIso_inv_snd_snd, pullbackSymmetry_hom_comp_fst_assoc
-/
theorem Periodic.neg_nat_mul [NonAssocRing α] (h : Periodic f c) (n : Nat) : Periodic f (-(n * c)) :=
  (h.nat_mul n).neg

/--
theorem `Periodic.sub_nsmul_eq` / 定理 `Periodic.sub_nsmul_eq`

English:
theorem Periodic.sub_nsmul_eq
  given: [AddGroup α] (h : Periodic f c) (n : Nat)
  statement: f (x - n • c) = f x
  proof: by
  simpa only [sub_eq_add_neg] using h.neg_nsmul n x

中文:
定理 周期.sub_nsmul_eq
  条件: [加法群 α] (h : 周期 f c) (n : 自然数)
  结论: f (x - n • c) = f x
  证明: by
  simpa only [sub_eq_add_neg] using h.neg_nsmul n x

Depends on / 依赖: Category, Category.assoc, h.neg_nsmul, lift_fst_assoc, neg_nsmul, pullback, pullback.lift_fst_assoc, pullbackRightPullbackFstIso_hom_fst_assoc, pullbackRightPullbackFstIso_inv_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc, sub_eq_add_neg, t_fst_fst
-/
theorem Periodic.sub_nsmul_eq [AddGroup α] (h : Periodic f c) (n : Nat) : f (x - n • c) = f x := by
  simpa only [sub_eq_add_neg] using h.neg_nsmul n x

/--
theorem `Periodic.sub_nat_mul_eq` / 定理 `Periodic.sub_nat_mul_eq`

English:
theorem Periodic.sub_nat_mul_eq
  given: [NonAssocRing α] (h : Periodic f c) (n : Nat)
  proof: by
  simpa only [nsmul_eq_mul] using h.sub_nsmul_eq n

中文:
定理 周期.sub_nat_mul_eq
  条件: [非结合环 α] (h : 周期 f c) (n : 自然数)
  证明: by
  simpa only [nsmul_eq_mul] using h.sub_nsmul_eq n

Depends on / 依赖: Category, Category.assoc, h.sub_nsmul_eq, lift_fst_assoc, nsmul_eq_mul, pullback, pullback.lift_fst_assoc, pullbackRightPullbackFstIso_hom_fst_assoc, pullbackRightPullbackFstIso_inv_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc, sub_nsmul_eq, t_fst_snd
-/
theorem Periodic.sub_nat_mul_eq [NonAssocRing α] (h : Periodic f c) (n : Nat) :
    f (x - n * c) = f x := by
  simpa only [nsmul_eq_mul] using h.sub_nsmul_eq n

/--
theorem `Periodic.nsmul_sub_eq` / 定理 `Periodic.nsmul_sub_eq`

English:
theorem Periodic.nsmul_sub_eq
  given: [SubtractionCommMonoid α] (h : Periodic f c) (n : Nat)
  proof: (h.nsmul n).sub_eq'

中文:
定理 周期.nsmul_sub_eq
  条件: [SubtractionComm幺半群 α] (h : 周期 f c) (n : 自然数)
  证明: (h.nsmul n).sub_eq'

Depends on / 依赖: Category, Category.assoc, h.nsmul, lift_fst_assoc, pullback, pullback.lift_fst_assoc, pullbackRightPullbackFstIso_hom_fst_assoc, pullbackRightPullbackFstIso_inv_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc, sub_eq, t_snd
-/
theorem Periodic.nsmul_sub_eq [SubtractionCommMonoid α] (h : Periodic f c) (n : Nat) :
    f (n • c - x) = f (-x) :=
  (h.nsmul n).sub_eq'

/--
theorem `Periodic.nat_mul_sub_eq` / 定理 `Periodic.nat_mul_sub_eq`

English:
theorem Periodic.nat_mul_sub_eq
  given: [NonAssocRing α] (h : Periodic f c) (n : Nat)
  proof: by
  simpa only [sub_eq_neg_add] using h.nat_mul n (-x)

中文:
定理 周期.nat_mul_sub_eq
  条件: [非结合环 α] (h : 周期 f c) (n : 自然数)
  证明: by
  simpa only [sub_eq_neg_add] using h.nat_mul n (-x)

Depends on / 依赖: h.nat_mul, nat_mul, sub_eq_neg_add
-/
theorem Periodic.nat_mul_sub_eq [NonAssocRing α] (h : Periodic f c) (n : Nat) :
    f (n * c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h.nat_mul n (-x)

/--
theorem `Periodic.zsmul` / 定理 `Periodic.zsmul`

English:
theorem Periodic.zsmul
  given: [AddGroup α] (h : Periodic f c) (n : Int)
  statement: Periodic f (n • c)
  proof: by
  rcases n with n | n
  · simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using h.nsmul n
  · simpa only [negSucc_zsmul] using (h.nsmul (n + 1)).neg

中文:
定理 周期.zsmul
  条件: [加法群 α] (h : 周期 f c) (n : 整数)
  结论: 周期 f (n • c)
  证明: by
  rcases n with n | n
  · simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using h.nsmul n
  · simpa only [negSucc_zsmul] using (h.nsmul (n + 1)).neg
-/
protected theorem Periodic.zsmul [AddGroup α] (h : Periodic f c) (n : Int) : Periodic f (n • c) := by
  rcases n with n | n
  · simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using h.nsmul n
  · simpa only [negSucc_zsmul] using (h.nsmul (n + 1)).neg

/--
theorem `Periodic.int_mul` / 定理 `Periodic.int_mul`

English:
theorem Periodic.int_mul
  given: [NonAssocRing α] (h : Periodic f c) (n : Int)
  proof: by
  simpa only [zsmul_eq_mul] using h.zsmul n

中文:
定理 周期.int_mul
  条件: [非结合环 α] (h : 周期 f c) (n : 整数)
  证明: by
  simpa only [zsmul_eq_mul] using h.zsmul n
-/
protected theorem Periodic.int_mul [NonAssocRing α] (h : Periodic f c) (n : Int) :
    Periodic f (n * c) := by
  simpa only [zsmul_eq_mul] using h.zsmul n

/--
theorem `Periodic.sub_zsmul_eq` / 定理 `Periodic.sub_zsmul_eq`

English:
theorem Periodic.sub_zsmul_eq
  given: [AddGroup α] (h : Periodic f c) (n : Int)
  statement: f (x - n • c) = f x
  proof: (h.zsmul n).sub_eq x

中文:
定理 周期.sub_zsmul_eq
  条件: [加法群 α] (h : 周期 f c) (n : 整数)
  结论: f (x - n • c) = f x
  证明: (h.zsmul n).sub_eq x

Depends on / 依赖: h.zsmul, sub_eq
-/
theorem Periodic.sub_zsmul_eq [AddGroup α] (h : Periodic f c) (n : Int) : f (x - n • c) = f x :=
  (h.zsmul n).sub_eq x

/--
theorem `Periodic.sub_int_mul_eq` / 定理 `Periodic.sub_int_mul_eq`

English:
theorem Periodic.sub_int_mul_eq
  given: [NonAssocRing α] (h : Periodic f c) (n : Int)
  statement: f (x - n * c) = f x
  proof: (h.int_mul n).sub_eq x

中文:
定理 周期.sub_int_mul_eq
  条件: [非结合环 α] (h : 周期 f c) (n : 整数)
  结论: f (x - n * c) = f x
  证明: (h.int_mul n).sub_eq x

Depends on / 依赖: h.int_mul, int_mul, sub_eq
-/
theorem Periodic.sub_int_mul_eq [NonAssocRing α] (h : Periodic f c) (n : Int) : f (x - n * c) = f x :=
  (h.int_mul n).sub_eq x

/--
theorem `Periodic.zsmul_sub_eq` / 定理 `Periodic.zsmul_sub_eq`

English:
theorem Periodic.zsmul_sub_eq
  given: [AddCommGroup α] (h : Periodic f c) (n : Int)
  proof: (h.zsmul _).sub_eq'

中文:
定理 周期.zsmul_sub_eq
  条件: [加法交换群 α] (h : 周期 f c) (n : 整数)
  证明: (h.zsmul _).sub_eq'

Depends on / 依赖: h.zsmul, sub_eq
-/
theorem Periodic.zsmul_sub_eq [AddCommGroup α] (h : Periodic f c) (n : Int) :
    f (n • c - x) = f (-x) :=
  (h.zsmul _).sub_eq'

/--
theorem `Periodic.int_mul_sub_eq` / 定理 `Periodic.int_mul_sub_eq`

English:
theorem Periodic.int_mul_sub_eq
  given: [NonAssocRing α] (h : Periodic f c) (n : Int)
  proof: (h.int_mul _).sub_eq'

中文:
定理 周期.int_mul_sub_eq
  条件: [非结合环 α] (h : 周期 f c) (n : 整数)
  证明: (h.int_mul _).sub_eq'

Depends on / 依赖: h.int_mul, int_mul, sub_eq
-/
theorem Periodic.int_mul_sub_eq [NonAssocRing α] (h : Periodic f c) (n : Int) :
    f (n * c - x) = f (-x) :=
  (h.int_mul _).sub_eq'

/--
theorem `Periodic.eq` / 定理 `Periodic.eq`

English:
theorem Periodic.eq
  given: [AddZeroClass α] (h : Periodic f c)
  statement: f c = f 0
  proof: by
  simpa only [zero_add] using h 0

中文:
定理 周期.eq
  条件: [加法零类 α] (h : 周期 f c)
  结论: f c = f 0
  证明: by
  simpa only [zero_add] using h 0
-/
protected theorem Periodic.eq [AddZeroClass α] (h : Periodic f c) : f c = f 0 := by
  simpa only [zero_add] using h 0

/--
theorem `Periodic.neg_eq` / 定理 `Periodic.neg_eq`

English:
theorem Periodic.neg_eq
  given: [AddGroup α] (h : Periodic f c)
  statement: f (-c) = f 0
  proof: h.neg.eq

中文:
定理 周期.neg_eq
  条件: [加法群 α] (h : 周期 f c)
  结论: f (-c) = f 0
  证明: h.neg.eq
-/
protected theorem Periodic.neg_eq [AddGroup α] (h : Periodic f c) : f (-c) = f 0 :=
  h.neg.eq

/--
theorem `Periodic.nsmul_eq` / 定理 `Periodic.nsmul_eq`

English:
theorem Periodic.nsmul_eq
  given: [AddMonoid α] (h : Periodic f c) (n : Nat)
  statement: f (n • c) = f 0
  proof: (h.nsmul n).eq

中文:
定理 周期.nsmul_eq
  条件: [加法幺半群 α] (h : 周期 f c) (n : 自然数)
  结论: f (n • c) = f 0
  证明: (h.nsmul n).eq
-/
protected theorem Periodic.nsmul_eq [AddMonoid α] (h : Periodic f c) (n : Nat) : f (n • c) = f 0 :=
  (h.nsmul n).eq

/--
theorem `Periodic.nat_mul_eq` / 定理 `Periodic.nat_mul_eq`

English:
theorem Periodic.nat_mul_eq
  given: [NonAssocSemiring α] (h : Periodic f c) (n : Nat)
  statement: f (n * c) = f 0
  proof: (h.nat_mul n).eq

中文:
定理 周期.nat_mul_eq
  条件: [非结合半环 α] (h : 周期 f c) (n : 自然数)
  结论: f (n * c) = f 0
  证明: (h.nat_mul n).eq

Depends on / 依赖: h.nat_mul, nat_mul
-/
theorem Periodic.nat_mul_eq [NonAssocSemiring α] (h : Periodic f c) (n : Nat) : f (n * c) = f 0 :=
  (h.nat_mul n).eq

/--
theorem `Periodic.zsmul_eq` / 定理 `Periodic.zsmul_eq`

English:
theorem Periodic.zsmul_eq
  given: [AddGroup α] (h : Periodic f c) (n : Int)
  statement: f (n • c) = f 0
  proof: (h.zsmul n).eq

中文:
定理 周期.zsmul_eq
  条件: [加法群 α] (h : 周期 f c) (n : 整数)
  结论: f (n • c) = f 0
  证明: (h.zsmul n).eq

Depends on / 依赖: h.zsmul
-/
theorem Periodic.zsmul_eq [AddGroup α] (h : Periodic f c) (n : Int) : f (n • c) = f 0 :=
  (h.zsmul n).eq

/--
theorem `Periodic.int_mul_eq` / 定理 `Periodic.int_mul_eq`

English:
theorem Periodic.int_mul_eq
  given: [NonAssocRing α] (h : Periodic f c) (n : Int)
  statement: f (n * c) = f 0
  proof: (h.int_mul n).eq

中文:
定理 周期.int_mul_eq
  条件: [非结合环 α] (h : 周期 f c) (n : 整数)
  结论: f (n * c) = f 0
  证明: (h.int_mul n).eq

Depends on / 依赖: h.int_mul, int_mul
-/
theorem Periodic.int_mul_eq [NonAssocRing α] (h : Periodic f c) (n : Int) : f (n * c) = f 0 :=
  (h.int_mul n).eq

/--
theorem `periodic_with_period_zero` / 定理 `periodic_with_period_zero`

English:
theorem periodic_with_period_zero
  given: [AddZeroClass α] (f : α -> β)
  statement: Periodic f 0
  proof: fun x => by
  rw [add_zero]

中文:
定理 periodic_with_period_zero
  条件: [加法零类 α] (f : α -> β)
  结论: 周期 f 0
  证明: fun x => by
  rw [add_zero]

Depends on / 依赖: add_zero
-/
theorem periodic_with_period_zero [AddZeroClass α] (f : α -> β) : Periodic f 0 := fun x => by
  rw [add_zero]

/--
theorem `periodic_iterate_iff` / 定理 `periodic_iterate_iff`

English:
theorem periodic_iterate_iff
  given: {f : α -> α} {n : Nat} {a : α}
  proof: by
  refine ⟨fun h => h.eq, fun h k => ?_⟩
  simp only [Function.iterate_add_apply, h.eq]

alias ⟨Periodic.isPeriodicPt, IsPeriodicPt.periodic_iterate⟩ := periodic_iterate_iff

中文:
定理 periodic_iterate_iff
  条件: {f : α -> α} {n : 自然数} {a : α}
  证明: by
  refine ⟨fun h => h.eq, fun h k => ?_⟩
  simp only [Function.iterate_add_apply, h.eq]

alias ⟨Periodic.isPeriodicPt, IsPeriodicPt.periodic_iterate⟩ := periodic_iterate_iff

Depends on / 依赖: Function, Function.iterate_add_apply, h.eq, iterate_add_apply
-/
theorem periodic_iterate_iff {f : α -> α} {n : Nat} {a : α} :
    Periodic (f^[·] a) n ↔ IsPeriodicPt f n a := by
  refine ⟨fun h => h.eq, fun h k => ?_⟩
  simp only [Function.iterate_add_apply, h.eq]

alias ⟨Periodic.isPeriodicPt, IsPeriodicPt.periodic_iterate⟩ := periodic_iterate_iff

/--
theorem `Periodic.map_vadd_zmultiples` / 定理 `Periodic.map_vadd_zmultiples`

English:
theorem Periodic.map_vadd_zmultiples
  statement: [AddCommGroup α] (hf : Periodic f c)
  proof: by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubgroup.vadd_def, add_comm _ x, hf.zsmul m x]

中文:
定理 周期.map_vadd_zmultiples
  结论: [加法交换群 α] (hf : 周期 f c)
  证明: by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubgroup.vadd_def, add_comm _ x, hf.zsmul m x]

Depends on / 依赖: AddSubgroup, AddSubgroup.vadd_def, add_comm, hf.zsmul, vadd_def
-/
theorem Periodic.map_vadd_zmultiples [AddCommGroup α] (hf : Periodic f c)
    (a : AddSubgroup.zmultiples c) (x : α) : f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubgroup.vadd_def, add_comm _ x, hf.zsmul m x]

/--
theorem `Periodic.map_vadd_multiples` / 定理 `Periodic.map_vadd_multiples`

English:
theorem Periodic.map_vadd_multiples
  statement: [AddCommMonoid α] (hf : Periodic f c)
  proof: by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubmonoid.vadd_def, add_comm _ x, hf.nsmul m x]

中文:
定理 周期.map_vadd_multiples
  结论: [加法交换幺半群 α] (hf : 周期 f c)
  证明: by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubmonoid.vadd_def, add_comm _ x, hf.nsmul m x]

Depends on / 依赖: AddSubmonoid, AddSubmonoid.vadd_def, add_comm, hf.nsmul, vadd_def
-/
theorem Periodic.map_vadd_multiples [AddCommMonoid α] (hf : Periodic f c)
    (a : AddSubmonoid.multiples c) (x : α) : f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubmonoid.vadd_def, add_comm _ x, hf.nsmul m x]

/--
Definition of `Periodic.lift` / `Periodic.lift` 的定义

English:
definition Periodic.lift
  signature: [AddGroup α] (h : Periodic f c) (x : α ⧸ AddSubgroup.zmultiples c)
  body: Quotient.liftOn' x f fun a b h' => by
    rw [QuotientAddGroup.leftRel_apply] at h'
    obtain ⟨k, hk⟩ := h'
    exact (h.zsmul k _).symm.trans (congr_arg f (add_eq_of_eq_neg_add hk))

@[simp]

中文:
定义 周期.lift
  签名: [加法群 α] (h : 周期 f c) (x : α ⧸ 加法子群.zmultiples c)
  定义体: Quotient.liftOn' x f fun a b h' => by
    rw [QuotientAddGroup.leftRel_apply] at h'
    obtain ⟨k, hk⟩ := h'
    exact (h.zsmul k _).symm.trans (congr_arg f (add_eq_of_eq_neg_add hk))

@[simp]

Depends on / 依赖: Quotient, Quotient.liftOn, QuotientAddGroup, QuotientAddGroup.leftRel_apply, add_eq_of_eq_neg_add, congr_arg, h.zsmul, leftRel_apply, liftOn, symm.trans
-/
def Periodic.lift [AddGroup α] (h : Periodic f c) (x : α ⧸ AddSubgroup.zmultiples c) : β :=
  Quotient.liftOn' x f fun a b h' => by
    rw [QuotientAddGroup.leftRel_apply] at h'
    obtain ⟨k, hk⟩ := h'
    exact (h.zsmul k _).symm.trans (congr_arg f (add_eq_of_eq_neg_add hk))

@[simp]
/--
theorem `Periodic.lift_coe` / 定理 `Periodic.lift_coe`

English:
theorem Periodic.lift_coe
  given: [AddGroup α] (h : Periodic f c) (a : α)
  proof: rfl

中文:
定理 周期.lift_coe
  条件: [加法群 α] (h : 周期 f c) (a : α)
  证明: rfl
-/
theorem Periodic.lift_coe [AddGroup α] (h : Periodic f c) (a : α) :
    h.lift (a : α ⧸ AddSubgroup.zmultiples c) = f a :=
  rfl

/--
lemma `Periodic.not_injective` / 引理 `Periodic.not_injective`

English:
lemma Periodic.not_injective
  statement: {R X : Type*} [AddZeroClass R] {f : R -> X} {c : R}
  proof: fun h => hc h hf.eq

中文:
引理 周期.not_injective
  结论: {R X : 类型} [加法零类 R] {f : R -> X} {c : R}
  证明: fun h => hc h hf.eq

Depends on / 依赖: hf.eq
-/
lemma Periodic.not_injective {R X : Type*} [AddZeroClass R] {f : R -> X} {c : R}
(hf : Periodic f c) (hc : c != 0) : ¬ Injective f := fun h => hc h hf.eq

/-! ### Antiperiodicity -/

/-- A function `f` is said to be `antiperiodic` with antiperiod `c` if for all `x`,
  `f (x + c) = -f x`. -/
@[simp]
/--
Definition of `Antiperiodic` / `Antiperiodic` 的定义

English:
definition Antiperiodic
  signature: [Add α] [Neg β] (f : α -> β) (c : α)
  body: forall x : α, f (x + c) = -f x

中文:
定义 Antiperiodic
  签名: [加法 α] [取负 β] (f : α -> β) (c : α)
  定义体: forall x : α, f (x + c) = -f x
-/
def Antiperiodic [Add α] [Neg β] (f : α -> β) (c : α) : Prop :=
  forall x : α, f (x + c) = -f x

/--
theorem `Antiperiodic.funext` / 定理 `Antiperiodic.funext`

English:
theorem Antiperiodic.funext
  given: [Add α] [Neg β] (h : Antiperiodic f c)
  proof: funext h

中文:
定理 Antiperiodic.funext
  条件: [加法 α] [取负 β] (h : Antiperiodic f c)
  证明: funext h
-/
protected theorem Antiperiodic.funext [Add α] [Neg β] (h : Antiperiodic f c) :
    (fun x => f (x + c)) = -f :=
  funext h

/--
theorem `Antiperiodic.funext'` / 定理 `Antiperiodic.funext'`

English:
theorem Antiperiodic.funext'
  given: [Add α] [InvolutiveNeg β] (h : Antiperiodic f c)
  proof: neg_eq_iff_eq_neg.mpr h.funext

中文:
定理 Antiperiodic.funext'
  条件: [加法 α] [InvolutiveNeg β] (h : Antiperiodic f c)
  证明: neg_eq_iff_eq_neg.mpr h.funext
-/
protected theorem Antiperiodic.funext' [Add α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    (fun x => -f (x + c)) = f :=
  neg_eq_iff_eq_neg.mpr h.funext

/--
theorem `Antiperiodic.periodic` / 定理 `Antiperiodic.periodic`

English:
theorem Antiperiodic.periodic
  statement: [AddMonoid α] [InvolutiveNeg β]
  proof: by simp [two_nsmul, ← add_assoc, h _]

中文:
定理 Antiperiodic.periodic
  结论: [加法幺半群 α] [InvolutiveNeg β]
  证明: by simp [two_nsmul, ← add_assoc, h _]
-/
protected theorem Antiperiodic.periodic [AddMonoid α] [InvolutiveNeg β]
    (h : Antiperiodic f c) : Periodic f (2 • c) := by simp [two_nsmul, ← add_assoc, h _]

/--
theorem `Antiperiodic.periodic_two_mul` / 定理 `Antiperiodic.periodic_two_mul`

English:
theorem Antiperiodic.periodic_two_mul
  statement: [NonAssocSemiring α] [InvolutiveNeg β]
  proof: nsmul_eq_mul 2 c ▸ h.periodic

中文:
定理 Antiperiodic.periodic_two_mul
  结论: [非结合半环 α] [InvolutiveNeg β]
  证明: nsmul_eq_mul 2 c ▸ h.periodic
-/
protected theorem Antiperiodic.periodic_two_mul [NonAssocSemiring α] [InvolutiveNeg β]
    (h : Antiperiodic f c) : Periodic f (2 * c) := nsmul_eq_mul 2 c ▸ h.periodic

/--
theorem `Antiperiodic.eq` / 定理 `Antiperiodic.eq`

English:
theorem Antiperiodic.eq
  given: [AddZeroClass α] [Neg β] (h : Antiperiodic f c)
  statement: f c = -f 0
  proof: by
  simpa only [zero_add] using h 0

中文:
定理 Antiperiodic.eq
  条件: [加法零类 α] [取负 β] (h : Antiperiodic f c)
  结论: f c = -f 0
  证明: by
  simpa only [zero_add] using h 0
-/
protected theorem Antiperiodic.eq [AddZeroClass α] [Neg β] (h : Antiperiodic f c) : f c = -f 0 := by
  simpa only [zero_add] using h 0

/--
theorem `Antiperiodic.even_nsmul_periodic` / 定理 `Antiperiodic.even_nsmul_periodic`

English:
theorem Antiperiodic.even_nsmul_periodic
  statement: [AddMonoid α] [InvolutiveNeg β] (h : Antiperiodic f c)
  proof: mul_nsmul c 2 n ▸ h.periodic.nsmul n

中文:
定理 Antiperiodic.even_nsmul_periodic
  结论: [加法幺半群 α] [InvolutiveNeg β] (h : Antiperiodic f c)
  证明: mul_nsmul c 2 n ▸ h.periodic.nsmul n

Depends on / 依赖: h.periodic.nsmul, mul_nsmul, periodic
-/
theorem Antiperiodic.even_nsmul_periodic [AddMonoid α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : Nat) : Periodic f ((2 * n) • c) := mul_nsmul c 2 n ▸ h.periodic.nsmul n

/--
theorem `Antiperiodic.nat_even_mul_periodic` / 定理 `Antiperiodic.nat_even_mul_periodic`

English:
theorem Antiperiodic.nat_even_mul_periodic
  statement: [NonAssocSemiring α] [InvolutiveNeg β]
  proof: h.periodic_two_mul.nat_mul n

中文:
定理 Antiperiodic.nat_even_mul_periodic
  结论: [非结合半环 α] [InvolutiveNeg β]
  证明: h.periodic_two_mul.nat_mul n

Depends on / 依赖: h.periodic_two_mul.nat_mul, nat_mul, periodic_two_mul
-/
theorem Antiperiodic.nat_even_mul_periodic [NonAssocSemiring α] [InvolutiveNeg β]
    (h : Antiperiodic f c) (n : Nat) : Periodic f (n * (2 * c)) :=
  h.periodic_two_mul.nat_mul n

/--
theorem `Antiperiodic.odd_nsmul_antiperiodic` / 定理 `Antiperiodic.odd_nsmul_antiperiodic`

English:
theorem Antiperiodic.odd_nsmul_antiperiodic
  statement: [AddMonoid α] [InvolutiveNeg β] (h : Antiperiodic f c)
  proof: fun x => by
  rw [add_nsmul]; rw [one_nsmul]; rw [← add_assoc]; rw [h]; rw [h.even_nsmul_periodic]

中文:
定理 Antiperiodic.odd_nsmul_antiperiodic
  结论: [加法幺半群 α] [InvolutiveNeg β] (h : Antiperiodic f c)
  证明: fun x => by
  rw [add_nsmul]; rw [one_nsmul]; rw [← add_assoc]; rw [h]; rw [h.even_nsmul_periodic]

Depends on / 依赖: add_assoc, add_nsmul, even_nsmul_periodic, h.even_nsmul_periodic, one_nsmul
-/
theorem Antiperiodic.odd_nsmul_antiperiodic [AddMonoid α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : Nat) : Antiperiodic f ((2 * n + 1) • c) := fun x => by
  rw [add_nsmul]; rw [one_nsmul]; rw [← add_assoc]; rw [h]; rw [h.even_nsmul_periodic]

/--
theorem `Antiperiodic.nat_odd_mul_antiperiodic` / 定理 `Antiperiodic.nat_odd_mul_antiperiodic`

English:
theorem Antiperiodic.nat_odd_mul_antiperiodic
  statement: [NonAssocSemiring α] [InvolutiveNeg β]
  proof: fun x => by
  rw [← add_assoc]; rw [h]; rw [h.nat_even_mul_periodic]

中文:
定理 Antiperiodic.nat_odd_mul_antiperiodic
  结论: [非结合半环 α] [InvolutiveNeg β]
  证明: fun x => by
  rw [← add_assoc]; rw [h]; rw [h.nat_even_mul_periodic]

Depends on / 依赖: add_assoc, h.nat_even_mul_periodic, nat_even_mul_periodic
-/
theorem Antiperiodic.nat_odd_mul_antiperiodic [NonAssocSemiring α] [InvolutiveNeg β]
    (h : Antiperiodic f c) (n : Nat) : Antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assoc]; rw [h]; rw [h.nat_even_mul_periodic]

/--
theorem `Antiperiodic.even_zsmul_periodic` / 定理 `Antiperiodic.even_zsmul_periodic`

English:
theorem Antiperiodic.even_zsmul_periodic
  statement: [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c)
  proof: by
  rw [mul_comm]; rw [mul_zsmul]; rw [two_zsmul]; rw [← two_nsmul]
  exact h.periodic.zsmul n

中文:
定理 Antiperiodic.even_zsmul_periodic
  结论: [加法群 α] [InvolutiveNeg β] (h : Antiperiodic f c)
  证明: by
  rw [mul_comm]; rw [mul_zsmul]; rw [two_zsmul]; rw [← two_nsmul]
  exact h.periodic.zsmul n

Depends on / 依赖: h.periodic.zsmul, mul_comm, mul_zsmul, periodic, two_nsmul, two_zsmul
-/
theorem Antiperiodic.even_zsmul_periodic [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : Int) : Periodic f ((2 * n) • c) := by
  rw [mul_comm]; rw [mul_zsmul]; rw [two_zsmul]; rw [← two_nsmul]
  exact h.periodic.zsmul n

/--
theorem `Antiperiodic.int_even_mul_periodic` / 定理 `Antiperiodic.int_even_mul_periodic`

English:
theorem Antiperiodic.int_even_mul_periodic
  statement: [NonAssocRing α] [InvolutiveNeg β] (h : Antiperiodic f c)
  proof: h.periodic_two_mul.int_mul n

中文:
定理 Antiperiodic.int_even_mul_periodic
  结论: [非结合环 α] [InvolutiveNeg β] (h : Antiperiodic f c)
  证明: h.periodic_two_mul.int_mul n

Depends on / 依赖: h.periodic_two_mul.int_mul, int_mul, periodic_two_mul
-/
theorem Antiperiodic.int_even_mul_periodic [NonAssocRing α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : Int) : Periodic f (n * (2 * c)) :=
  h.periodic_two_mul.int_mul n

/--
theorem `Antiperiodic.odd_zsmul_antiperiodic` / 定理 `Antiperiodic.odd_zsmul_antiperiodic`

English:
theorem Antiperiodic.odd_zsmul_antiperiodic
  statement: [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c)
  proof: by
  intro x
  rw [add_zsmul]; rw [one_zsmul]; rw [← add_assoc]; rw [h]; rw [h.even_zsmul_periodic]

中文:
定理 Antiperiodic.odd_zsmul_antiperiodic
  结论: [加法群 α] [InvolutiveNeg β] (h : Antiperiodic f c)
  证明: by
  intro x
  rw [add_zsmul]; rw [one_zsmul]; rw [← add_assoc]; rw [h]; rw [h.even_zsmul_periodic]

Depends on / 依赖: add_assoc, add_zsmul, even_zsmul_periodic, h.even_zsmul_periodic, one_zsmul
-/
theorem Antiperiodic.odd_zsmul_antiperiodic [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : Int) : Antiperiodic f ((2 * n + 1) • c) := by
  intro x
  rw [add_zsmul]; rw [one_zsmul]; rw [← add_assoc]; rw [h]; rw [h.even_zsmul_periodic]

/--
theorem `Antiperiodic.int_odd_mul_antiperiodic` / 定理 `Antiperiodic.int_odd_mul_antiperiodic`

English:
theorem Antiperiodic.int_odd_mul_antiperiodic
  statement: [NonAssocRing α] [InvolutiveNeg β]
  proof: fun x => by
  rw [← add_assoc]; rw [h]; rw [h.int_even_mul_periodic]

中文:
定理 Antiperiodic.int_odd_mul_antiperiodic
  结论: [非结合环 α] [InvolutiveNeg β]
  证明: fun x => by
  rw [← add_assoc]; rw [h]; rw [h.int_even_mul_periodic]

Depends on / 依赖: add_assoc, h.int_even_mul_periodic, int_even_mul_periodic
-/
theorem Antiperiodic.int_odd_mul_antiperiodic [NonAssocRing α] [InvolutiveNeg β]
    (h : Antiperiodic f c) (n : Int) : Antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assoc]; rw [h]; rw [h.int_even_mul_periodic]

/--
theorem `Antiperiodic.sub_eq` / 定理 `Antiperiodic.sub_eq`

English:
theorem Antiperiodic.sub_eq
  given: [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) (x : α)
  proof: by simp only [← neg_eq_iff_eq_neg, ← h (x - c), sub_add_cancel]

中文:
定理 Antiperiodic.sub_eq
  条件: [加法群 α] [InvolutiveNeg β] (h : Antiperiodic f c) (x : α)
  证明: by simp only [← neg_eq_iff_eq_neg, ← h (x - c), sub_add_cancel]

Depends on / 依赖: Z.affineCover.pullback, affineCover, hasPullback_of_cover, neg_eq_iff_eq_neg, sub_add_cancel
-/
theorem Antiperiodic.sub_eq [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) (x : α) :
    f (x - c) = -f x := by simp only [← neg_eq_iff_eq_neg, ← h (x - c), sub_add_cancel]

/--
theorem `Antiperiodic.sub_eq'` / 定理 `Antiperiodic.sub_eq'`

English:
theorem Antiperiodic.sub_eq'
  given: [SubtractionCommMonoid α] [Neg β] (h : Antiperiodic f c)
  proof: by simpa only [sub_eq_neg_add] using h (-x)

中文:
定理 Antiperiodic.sub_eq'
  条件: [SubtractionComm幺半群 α] [取负 β] (h : Antiperiodic f c)
  证明: by simpa only [sub_eq_neg_add] using h (-x)

Depends on / 依赖: sub_eq_neg_add
-/
theorem Antiperiodic.sub_eq' [SubtractionCommMonoid α] [Neg β] (h : Antiperiodic f c) :
    f (c - x) = -f (-x) := by simpa only [sub_eq_neg_add] using h (-x)

/--
theorem `Antiperiodic.neg` / 定理 `Antiperiodic.neg`

English:
theorem Antiperiodic.neg
  given: [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c)
  proof: by simpa only [sub_eq_add_neg, Antiperiodic] using h.sub_eq

中文:
定理 Antiperiodic.neg
  条件: [加法群 α] [InvolutiveNeg β] (h : Antiperiodic f c)
  证明: by simpa only [sub_eq_add_neg, Antiperiodic] using h.sub_eq
-/
protected theorem Antiperiodic.neg [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    Antiperiodic f (-c) := by simpa only [sub_eq_add_neg, Antiperiodic] using h.sub_eq

/--
theorem `Antiperiodic.neg_eq` / 定理 `Antiperiodic.neg_eq`

English:
theorem Antiperiodic.neg_eq
  given: [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c)
  proof: by
  simpa only [zero_add] using h.neg 0

中文:
定理 Antiperiodic.neg_eq
  条件: [加法群 α] [InvolutiveNeg β] (h : Antiperiodic f c)
  证明: by
  simpa only [zero_add] using h.neg 0

Depends on / 依赖: h.neg, zero_add
-/
theorem Antiperiodic.neg_eq [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    f (-c) = -f 0 := by
  simpa only [zero_add] using h.neg 0

/--
theorem `Antiperiodic.nat_mul_eq_of_eq_zero` / 定理 `Antiperiodic.nat_mul_eq_of_eq_zero`

English:
theorem Antiperiodic.nat_mul_eq_of_eq_zero
  statement: [NonAssocSemiring α] [NegZeroClass β]

中文:
定理 Antiperiodic.nat_mul_eq_of_eq_zero
  结论: [非结合半环 α] [NegZero类 β]
-/
theorem Antiperiodic.nat_mul_eq_of_eq_zero [NonAssocSemiring α] [NegZeroClass β]
    (h : Antiperiodic f c) (hi : f 0 = 0) : forall n : Nat, f (n * c) = 0
  | 0 => by rwa [Nat.cast_zero, zero_mul]
  | n + 1 => by simp [add_mul, h _, Antiperiodic.nat_mul_eq_of_eq_zero h hi n]

/--
theorem `Antiperiodic.int_mul_eq_of_eq_zero` / 定理 `Antiperiodic.int_mul_eq_of_eq_zero`

English:
theorem Antiperiodic.int_mul_eq_of_eq_zero
  statement: [NonAssocRing α] [SubtractionMonoid β]

中文:
定理 Antiperiodic.int_mul_eq_of_eq_zero
  结论: [非结合环 α] [Subtraction幺半群 β]
-/
theorem Antiperiodic.int_mul_eq_of_eq_zero [NonAssocRing α] [SubtractionMonoid β]
    (h : Antiperiodic f c) (hi : f 0 = 0) : forall n : Int, f (n * c) = 0
  | (n : Nat) => by rw [Int.cast_natCast, h.nat_mul_eq_of_eq_zero hi n]
  | .negSucc n => by rw [Int.cast_negSucc, neg_mul, ← mul_neg, h.neg.nat_mul_eq_of_eq_zero hi]

/--
theorem `Antiperiodic.add_zsmul_eq` / 定理 `Antiperiodic.add_zsmul_eq`

English:
theorem Antiperiodic.add_zsmul_eq
  statement: [AddGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
  proof: by
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [h.even_zsmul_periodic, Int.negOnePow_two_mul, Units.val_one, one_zsmul]
  · rw [h.odd_zsmul_antiperiodic, Int.negOnePow_two_mul_add_one, Units.val_neg,
      Units.val_one, neg_zsmul, one_zsmul]

中文:
定理 Antiperiodic.add_zsmul_eq
  结论: [加法群 α] [Subtraction幺半群 β] (h : Antiperiodic f c)
  证明: by
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [h.even_zsmul_periodic, Int.negOnePow_two_mul, Units.val_one, one_zsmul]
  · rw [h.odd_zsmul_antiperiodic, Int.negOnePow_two_mul_add_one, Units.val_neg,
      Units.val_one, neg_zsmul, one_zsmul]

Depends on / 依赖: Int.even_or_odd, Int.negOnePow_two_mul, Int.negOnePow_two_mul_add_one, Units.val_neg, Units.val_one, even_or_odd, even_zsmul_periodic, h.even_zsmul_periodic, h.odd_zsmul_antiperiodic, negOnePow_two_mul, negOnePow_two_mul_add_one, neg_zsmul, odd_zsmul_antiperiodic, one_zsmul, val_neg, val_one
-/
theorem Antiperiodic.add_zsmul_eq [AddGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (n : Int) : f (x + n • c) = (n.negOnePow : Int) • f x := by
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [h.even_zsmul_periodic, Int.negOnePow_two_mul, Units.val_one, one_zsmul]
  · rw [h.odd_zsmul_antiperiodic, Int.negOnePow_two_mul_add_one, Units.val_neg,
      Units.val_one, neg_zsmul, one_zsmul]

/--
theorem `Antiperiodic.sub_zsmul_eq` / 定理 `Antiperiodic.sub_zsmul_eq`

English:
theorem Antiperiodic.sub_zsmul_eq
  statement: [AddGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
  proof: by
  simpa only [sub_eq_add_neg, neg_zsmul, Int.negOnePow_neg] using h.add_zsmul_eq (-n)

中文:
定理 Antiperiodic.sub_zsmul_eq
  结论: [加法群 α] [Subtraction幺半群 β] (h : Antiperiodic f c)
  证明: by
  simpa only [sub_eq_add_neg, neg_zsmul, Int.negOnePow_neg] using h.add_zsmul_eq (-n)

Depends on / 依赖: Int.negOnePow_neg, add_zsmul_eq, h.add_zsmul_eq, negOnePow_neg, neg_zsmul, sub_eq_add_neg
-/
theorem Antiperiodic.sub_zsmul_eq [AddGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (n : Int) : f (x - n • c) = (n.negOnePow : Int) • f x := by
  simpa only [sub_eq_add_neg, neg_zsmul, Int.negOnePow_neg] using h.add_zsmul_eq (-n)

/--
theorem `Antiperiodic.zsmul_sub_eq` / 定理 `Antiperiodic.zsmul_sub_eq`

English:
theorem Antiperiodic.zsmul_sub_eq
  statement: [AddCommGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
  proof: by
  rw [sub_eq_add_neg]; rw [add_comm]
  exact h.add_zsmul_eq n

中文:
定理 Antiperiodic.zsmul_sub_eq
  结论: [加法交换群 α] [Subtraction幺半群 β] (h : Antiperiodic f c)
  证明: by
  rw [sub_eq_add_neg]; rw [add_comm]
  exact h.add_zsmul_eq n

Depends on / 依赖: add_comm, add_zsmul_eq, h.add_zsmul_eq, sub_eq_add_neg
-/
theorem Antiperiodic.zsmul_sub_eq [AddCommGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (n : Int) : f (n • c - x) = (n.negOnePow : Int) • f (-x) := by
  rw [sub_eq_add_neg]; rw [add_comm]
  exact h.add_zsmul_eq n

/--
theorem `Antiperiodic.add_int_mul_eq` / 定理 `Antiperiodic.add_int_mul_eq`

English:
theorem Antiperiodic.add_int_mul_eq
  statement: [NonAssocRing α] [NonAssocRing β] (h : Antiperiodic f c)
  proof: by
  simpa only [zsmul_eq_mul] using h.add_zsmul_eq n

中文:
定理 Antiperiodic.add_int_mul_eq
  结论: [非结合环 α] [非结合环 β] (h : Antiperiodic f c)
  证明: by
  simpa only [zsmul_eq_mul] using h.add_zsmul_eq n

Depends on / 依赖: add_zsmul_eq, h.add_zsmul_eq, zsmul_eq_mul
-/
theorem Antiperiodic.add_int_mul_eq [NonAssocRing α] [NonAssocRing β] (h : Antiperiodic f c)
    (n : Int) : f (x + n * c) = (n.negOnePow : Int) * f x := by
  simpa only [zsmul_eq_mul] using h.add_zsmul_eq n

/--
theorem `Antiperiodic.sub_int_mul_eq` / 定理 `Antiperiodic.sub_int_mul_eq`

English:
theorem Antiperiodic.sub_int_mul_eq
  statement: [NonAssocRing α] [NonAssocRing β] (h : Antiperiodic f c)
  proof: by
  simpa only [zsmul_eq_mul] using h.sub_zsmul_eq n

中文:
定理 Antiperiodic.sub_int_mul_eq
  结论: [非结合环 α] [非结合环 β] (h : Antiperiodic f c)
  证明: by
  simpa only [zsmul_eq_mul] using h.sub_zsmul_eq n

Depends on / 依赖: h.sub_zsmul_eq, sub_zsmul_eq, zsmul_eq_mul
-/
theorem Antiperiodic.sub_int_mul_eq [NonAssocRing α] [NonAssocRing β] (h : Antiperiodic f c)
    (n : Int) : f (x - n * c) = (n.negOnePow : Int) * f x := by
  simpa only [zsmul_eq_mul] using h.sub_zsmul_eq n

/--
theorem `Antiperiodic.int_mul_sub_eq` / 定理 `Antiperiodic.int_mul_sub_eq`

English:
theorem Antiperiodic.int_mul_sub_eq
  statement: [NonAssocRing α] [NonAssocRing β] (h : Antiperiodic f c)
  proof: by
  simpa only [zsmul_eq_mul] using h.zsmul_sub_eq n

中文:
定理 Antiperiodic.int_mul_sub_eq
  结论: [非结合环 α] [非结合环 β] (h : Antiperiodic f c)
  证明: by
  simpa only [zsmul_eq_mul] using h.zsmul_sub_eq n

Depends on / 依赖: h.zsmul_sub_eq, zsmul_eq_mul, zsmul_sub_eq
-/
theorem Antiperiodic.int_mul_sub_eq [NonAssocRing α] [NonAssocRing β] (h : Antiperiodic f c)
    (n : Int) : f (n * c - x) = (n.negOnePow : Int) * f (-x) := by
  simpa only [zsmul_eq_mul] using h.zsmul_sub_eq n

/--
theorem `Antiperiodic.add_nsmul_eq` / 定理 `Antiperiodic.add_nsmul_eq`

English:
theorem Antiperiodic.add_nsmul_eq
  statement: [AddMonoid α] [SubtractionMonoid β] (h : Antiperiodic f c)
  proof: by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [h.even_nsmul_periodic]
    simp
  · rw [h.odd_nsmul_antiperiodic]
    simp [pow_add]

中文:
定理 Antiperiodic.add_nsmul_eq
  结论: [加法幺半群 α] [Subtraction幺半群 β] (h : Antiperiodic f c)
  证明: by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [h.even_nsmul_periodic]
    simp
  · rw [h.odd_nsmul_antiperiodic]
    simp [pow_add]

Depends on / 依赖: Nat.even_or_odd, even_nsmul_periodic, even_or_odd, h.even_nsmul_periodic, h.odd_nsmul_antiperiodic, odd_nsmul_antiperiodic, pow_add
-/
theorem Antiperiodic.add_nsmul_eq [AddMonoid α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (n : Nat) : f (x + n • c) = (-1) ^ n • f x := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [h.even_nsmul_periodic]
    simp
  · rw [h.odd_nsmul_antiperiodic]
    simp [pow_add]

/--
theorem `Antiperiodic.sub_nsmul_eq` / 定理 `Antiperiodic.sub_nsmul_eq`

English:
theorem Antiperiodic.sub_nsmul_eq
  statement: [AddGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
  proof: by
  simpa only [Int.reduceNeg, natCast_zsmul] using! h.sub_zsmul_eq n

中文:
定理 Antiperiodic.sub_nsmul_eq
  结论: [加法群 α] [Subtraction幺半群 β] (h : Antiperiodic f c)
  证明: by
  simpa only [Int.reduceNeg, natCast_zsmul] using! h.sub_zsmul_eq n

Depends on / 依赖: Int.reduceNeg, h.sub_zsmul_eq, natCast_zsmul, reduceNeg, sub_zsmul_eq
-/
theorem Antiperiodic.sub_nsmul_eq [AddGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (n : Nat) : f (x - n • c) = (-1) ^ n • f x := by
  simpa only [Int.reduceNeg, natCast_zsmul] using! h.sub_zsmul_eq n

/--
theorem `Antiperiodic.nsmul_sub_eq` / 定理 `Antiperiodic.nsmul_sub_eq`

English:
theorem Antiperiodic.nsmul_sub_eq
  statement: [AddCommGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
  proof: by
  simpa only [Int.reduceNeg, natCast_zsmul] using! h.zsmul_sub_eq n

中文:
定理 Antiperiodic.nsmul_sub_eq
  结论: [加法交换群 α] [Subtraction幺半群 β] (h : Antiperiodic f c)
  证明: by
  simpa only [Int.reduceNeg, natCast_zsmul] using! h.zsmul_sub_eq n

Depends on / 依赖: Int.reduceNeg, h.zsmul_sub_eq, natCast_zsmul, reduceNeg, zsmul_sub_eq
-/
theorem Antiperiodic.nsmul_sub_eq [AddCommGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (n : Nat) : f (n • c - x) = (-1) ^ n • f (-x) := by
  simpa only [Int.reduceNeg, natCast_zsmul] using! h.zsmul_sub_eq n

/--
theorem `Antiperiodic.const_add` / 定理 `Antiperiodic.const_add`

English:
theorem Antiperiodic.const_add
  given: [AddSemigroup α] [Neg β] (h : Antiperiodic f c) (a : α)
  proof: fun x => by simpa [add_assoc] using h (a + x)

中文:
定理 Antiperiodic.const_add
  条件: [加法半群 α] [取负 β] (h : Antiperiodic f c) (a : α)
  证明: fun x => by simpa [add_assoc] using h (a + x)

Depends on / 依赖: add_assoc
-/
theorem Antiperiodic.const_add [AddSemigroup α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (a + x)) c := fun x => by simpa [add_assoc] using h (a + x)

/--
theorem `Antiperiodic.add_const` / 定理 `Antiperiodic.add_const`

English:
theorem Antiperiodic.add_const
  given: [AddCommSemigroup α] [Neg β] (h : Antiperiodic f c) (a : α)
  proof: fun x => by
  simpa only [add_right_comm] using h (x + a)

中文:
定理 Antiperiodic.add_const
  条件: [加法交换半群 α] [取负 β] (h : Antiperiodic f c) (a : α)
  证明: fun x => by
  simpa only [add_right_comm] using h (x + a)

Depends on / 依赖: add_right_comm
-/
theorem Antiperiodic.add_const [AddCommSemigroup α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (x + a)) c := fun x => by
  simpa only [add_right_comm] using h (x + a)

/--
theorem `Antiperiodic.const_sub` / 定理 `Antiperiodic.const_sub`

English:
theorem Antiperiodic.const_sub
  given: [AddCommGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) (a : α)
  proof: fun x => by
  simp only [← sub_sub, h.sub_eq]

中文:
定理 Antiperiodic.const_sub
  条件: [加法交换群 α] [InvolutiveNeg β] (h : Antiperiodic f c) (a : α)
  证明: fun x => by
  simp only [← sub_sub, h.sub_eq]

Depends on / 依赖: h.sub_eq, sub_eq, sub_sub
-/
theorem Antiperiodic.const_sub [AddCommGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (a - x)) c := fun x => by
  simp only [← sub_sub, h.sub_eq]

/--
theorem `Antiperiodic.sub_const` / 定理 `Antiperiodic.sub_const`

English:
theorem Antiperiodic.sub_const
  given: [SubtractionCommMonoid α] [Neg β] (h : Antiperiodic f c) (a : α)
  proof: by
  simpa only [sub_eq_add_neg] using h.add_const (-a)

中文:
定理 Antiperiodic.sub_const
  条件: [SubtractionComm幺半群 α] [取负 β] (h : Antiperiodic f c) (a : α)
  证明: by
  simpa only [sub_eq_add_neg] using h.add_const (-a)

Depends on / 依赖: add_const, h.add_const, sub_eq_add_neg
-/
theorem Antiperiodic.sub_const [SubtractionCommMonoid α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (x - a)) c := by
  simpa only [sub_eq_add_neg] using h.add_const (-a)

/--
theorem `Antiperiodic.smul` / 定理 `Antiperiodic.smul`

English:
theorem Antiperiodic.smul
  statement: [Add α] [Monoid γ] [AddGroup β] [DistribMulAction γ β]
  proof: by simp_all

中文:
定理 Antiperiodic.smul
  结论: [加法 α] [幺半群 γ] [加法群 β] [分配乘法作用 γ β]
  证明: by simp_all
-/
theorem Antiperiodic.smul [Add α] [Monoid γ] [AddGroup β] [DistribMulAction γ β]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (a • f) c := by simp_all

/--
theorem `Antiperiodic.const_smul` / 定理 `Antiperiodic.const_smul`

English:
theorem Antiperiodic.const_smul
  statement: [AddMonoid α] [Neg β] [Group γ] [DistribMulAction γ α]
  proof: fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)

中文:
定理 Antiperiodic.const_smul
  结论: [加法幺半群 α] [取负 β] [群 γ] [分配乘法作用 γ α]
  证明: fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)

Depends on / 依赖: smul_add, smul_inv_smul
-/
theorem Antiperiodic.const_smul [AddMonoid α] [Neg β] [Group γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)

/--
theorem `Antiperiodic.const_inv_smul` / 定理 `Antiperiodic.const_inv_smul`

English:
theorem Antiperiodic.const_inv_smul
  statement: [AddMonoid α] [Neg β] [Group γ] [DistribMulAction γ α]
  proof: by
  simpa only [inv_inv] using h.const_smul a⁻¹

中文:
定理 Antiperiodic.const_inv_smul
  结论: [加法幺半群 α] [取负 β] [群 γ] [分配乘法作用 γ α]
  证明: by
  simpa only [inv_inv] using h.const_smul a⁻¹

Depends on / 依赖: const_smul, h.const_smul, inv_inv
-/
theorem Antiperiodic.const_inv_smul [AddMonoid α] [Neg β] [Group γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul a⁻¹

/--
theorem `Antiperiodic.add` / 定理 `Antiperiodic.add`

English:
theorem Antiperiodic.add
  statement: [AddSemigroup α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
  proof: by simp_all [← add_assoc]

中文:
定理 Antiperiodic.add
  结论: [加法半群 α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
  证明: by simp_all [← add_assoc]

Depends on / 依赖: add_assoc
-/
theorem Antiperiodic.add [AddSemigroup α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
    (h2 : Antiperiodic f c₂) : Periodic f (c₁ + c₂) := by simp_all [← add_assoc]

/--
theorem `Antiperiodic.sub` / 定理 `Antiperiodic.sub`

English:
theorem Antiperiodic.sub
  statement: [AddGroup α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
  proof: by
  simpa only [sub_eq_add_neg] using h1.add h2.neg

中文:
定理 Antiperiodic.sub
  结论: [加法群 α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
  证明: by
  simpa only [sub_eq_add_neg] using h1.add h2.neg

Depends on / 依赖: h1.add, h2.neg, sub_eq_add_neg
-/
theorem Antiperiodic.sub [AddGroup α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
    (h2 : Antiperiodic f c₂) : Periodic f (c₁ - c₂) := by
  simpa only [sub_eq_add_neg] using h1.add h2.neg

/--
theorem `Periodic.add_antiperiod` / 定理 `Periodic.add_antiperiod`

English:
theorem Periodic.add_antiperiod
  statement: [AddSemigroup α] [Neg β] (h1 : Periodic f c₁)
  proof: by simp_all [← add_assoc]

中文:
定理 周期.add_antiperiod
  结论: [加法半群 α] [取负 β] (h1 : 周期 f c₁)
  证明: by simp_all [← add_assoc]

Depends on / 依赖: add_assoc
-/
theorem Periodic.add_antiperiod [AddSemigroup α] [Neg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : Antiperiodic f (c₁ + c₂) := by simp_all [← add_assoc]

/--
theorem `Periodic.sub_antiperiod` / 定理 `Periodic.sub_antiperiod`

English:
theorem Periodic.sub_antiperiod
  statement: [AddGroup α] [InvolutiveNeg β] (h1 : Periodic f c₁)
  proof: by
  simpa only [sub_eq_add_neg] using h1.add_antiperiod h2.neg

中文:
定理 周期.sub_antiperiod
  结论: [加法群 α] [InvolutiveNeg β] (h1 : 周期 f c₁)
  证明: by
  simpa only [sub_eq_add_neg] using h1.add_antiperiod h2.neg

Depends on / 依赖: add_antiperiod, h1.add_antiperiod, h2.neg, sub_eq_add_neg
-/
theorem Periodic.sub_antiperiod [AddGroup α] [InvolutiveNeg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : Antiperiodic f (c₁ - c₂) := by
  simpa only [sub_eq_add_neg] using h1.add_antiperiod h2.neg

/--
theorem `Periodic.add_antiperiod_eq` / 定理 `Periodic.add_antiperiod_eq`

English:
theorem Periodic.add_antiperiod_eq
  statement: [AddMonoid α] [Neg β] (h1 : Periodic f c₁)
  proof: (h1.add_antiperiod h2).eq

中文:
定理 周期.add_antiperiod_eq
  结论: [加法幺半群 α] [取负 β] (h1 : 周期 f c₁)
  证明: (h1.add_antiperiod h2).eq

Depends on / 依赖: add_antiperiod, h1.add_antiperiod
-/
theorem Periodic.add_antiperiod_eq [AddMonoid α] [Neg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : f (c₁ + c₂) = -f 0 :=
  (h1.add_antiperiod h2).eq

/--
theorem `Periodic.sub_antiperiod_eq` / 定理 `Periodic.sub_antiperiod_eq`

English:
theorem Periodic.sub_antiperiod_eq
  statement: [AddGroup α] [InvolutiveNeg β] (h1 : Periodic f c₁)
  proof: (h1.sub_antiperiod h2).eq

中文:
定理 周期.sub_antiperiod_eq
  结论: [加法群 α] [InvolutiveNeg β] (h1 : 周期 f c₁)
  证明: (h1.sub_antiperiod h2).eq

Depends on / 依赖: h1.sub_antiperiod, sub_antiperiod
-/
theorem Periodic.sub_antiperiod_eq [AddGroup α] [InvolutiveNeg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : f (c₁ - c₂) = -f 0 :=
  (h1.sub_antiperiod h2).eq

/--
theorem `Antiperiodic.mul` / 定理 `Antiperiodic.mul`

English:
theorem Antiperiodic.mul
  statement: [Add α] [Mul β] [HasDistribNeg β] (hf : Antiperiodic f c)
  proof: by simp_all

中文:
定理 Antiperiodic.mul
  结论: [加法 α] [乘法 β] [有DistribNeg β] (hf : Antiperiodic f c)
  证明: by simp_all
-/
theorem Antiperiodic.mul [Add α] [Mul β] [HasDistribNeg β] (hf : Antiperiodic f c)
    (hg : Antiperiodic g c) : Periodic (f * g) c := by simp_all

/--
theorem `Antiperiodic.div` / 定理 `Antiperiodic.div`

English:
theorem Antiperiodic.div
  statement: [Add α] [DivisionMonoid β] [HasDistribNeg β] (hf : Antiperiodic f c)
  proof: by simp_all [neg_div_neg_eq]

中文:
定理 Antiperiodic.div
  结论: [加法 α] [Division幺半群 β] [有DistribNeg β] (hf : Antiperiodic f c)
  证明: by simp_all [neg_div_neg_eq]

Depends on / 依赖: neg_div_neg_eq
-/
theorem Antiperiodic.div [Add α] [DivisionMonoid β] [HasDistribNeg β] (hf : Antiperiodic f c)
    (hg : Antiperiodic g c) : Periodic (f / g) c := by simp_all [neg_div_neg_eq]

/--
theorem `Antiperiodic.sum_map_addRightEmbedding` / 定理 `Antiperiodic.sum_map_addRightEmbedding`

English:
theorem Antiperiodic.sum_map_addRightEmbedding
  statement: [Add α] [IsRightCancelAdd α]
  proof: by
  simp [hf _]

中文:
定理 Antiperiodic.sum_map_addRightEmbedding
  结论: [加法 α] [是右消去加法 α]
  证明: by
  simp [hf _]
-/
theorem Antiperiodic.sum_map_addRightEmbedding [Add α] [IsRightCancelAdd α]
    [SubtractionCommMonoid β] (hf : Antiperiodic f c) (s : Finset α) :
    ∑ k in s.map (addRightEmbedding c), f k = -∑ k in s, f k := by
  simp [hf _]

end Function
