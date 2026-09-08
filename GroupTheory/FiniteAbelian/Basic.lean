/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
module

public import Mathlib.Algebra.Module.PID
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.QuotientRing

/-!
# Structure of finite(ly generated) abelian groups

* `AddCommGroup.equiv_free_prod_directSum_zmod` : Any finitely generated abelian group is the
  product of a power of `ℤ` and a direct sum of some `ZMod (p i ^ e i)` for some prime powers
  `p i ^ e i`.
* `CommGroup.equiv_free_prod_prod_multiplicative_zmod` is a version for multiplicative groups.
* `AddCommGroup.equiv_directSum_zmod_of_finite` : Any finite abelian group is a direct sum of
  some `ZMod (p i ^ e i)` for some prime powers `p i ^ e i`.
* `CommGroup.equiv_prod_multiplicative_zmod_of_finite` is a version for multiplicative groups.
-/

@[expose] public section

open scoped DirectSum

/-
TODO: Here's a more general approach to dropping trivial factors from a direct sum:

def DirectSum.congr {ι κ : Type*} {α : ι → Type*} {β : κ → Type*} [DecidableEq ι] [DecidableEq κ]
    [∀ i, DecidableEq (α i)] [∀ j, DecidableEq (β j)] [∀ i, AddCommMonoid (α i)]
    [∀ j, AddCommMonoid (β j)] (f : ∀ i, Nontrivial (α i) → κ) (g : ∀ j, Nontrivial (β j) → ι)
    (F : ∀ i hi, α i →+ β (f i hi)) (G : ∀ j hj, β j →+ α (g j hj))
    (hfg : ∀ i hi hj, g (f i hi) hj = i) (hgf : ∀ j hj hi, f (g j hj) hi = j)
    (hFG : ∀ i hi hj a, hfg i hi hj ▸ G _ hj (F i hi a) = a)
    (hGF : ∀ j hj hi b, hgf j hj hi ▸ F _ hi (G j hj b) = b) :
    (⨁ i, α i) ≃+ ⨁ j, β j where
  toFun x := x.sum fun i a ↦ if ha : a = 0 then 0 else DFinsupp.single (f i ⟨a, 0, ha⟩) (F _ _ a)
  invFun y := y.sum fun j b ↦ if hb : b = 0 then 0 else DFinsupp.single (g j ⟨b, 0, hb⟩) (G _ _ b)
  -- The two sorries here are probably doable with the existing machinery, but quite painful
  left_inv x := DFinsupp.ext fun i ↦ sorry
  right_inv y := DFinsupp.ext fun j ↦ sorry
  map_add' x₁ x₂ := by
    dsimp
    refine DFinsupp.sum_add_index (by simp) fun i a₁ a₂ ↦ ?_
    split_ifs
    any_goals simp_all
    rw [← DFinsupp.single_add, ← map_add, ‹a₁ + a₂ = 0›, map_zero, DFinsupp.single_zero]

private def directSumNeZeroMulEquiv (ι : Type) [DecidableEq ι] (p : ι → ℕ) (n : ι → ℕ) :
    (⨁ i : {i // n i ≠ 0}, ZMod (p i ^ n i)) ≃+ ⨁ i, ZMod (p i ^ n i) :=
  DirectSum.congr
    (fun i _ ↦ i)
    (fun j hj ↦ ⟨j, fun h ↦ by simp [h, pow_zero, zmod_nontrivial] at hj⟩)
    (fun i _ ↦ AddMonoidHom.id _)
    (fun j _ ↦ AddMonoidHom.id _)
    (fun i hi hj ↦ rfl)
    (fun j hj hi ↦ rfl)
    (fun i hi hj a ↦ rfl)
    (fun j hj hi a ↦ rfl)
-/

/-
**directSumNeZeroMulHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
TODO: Here's a more general approach to dropping trivial factors from a direct s
um:

def DirectSum.congr {ι κ : Type*} {α : ι → Type*} {β : κ → Type*} [DecidableEq ι
] [DecidableEq κ]
    [∀ i, DecidableEq (α i)] [∀ j, DecidableEq (β j)] [∀ i, AddCommMonoid (α i)]
    [∀ j, AddCommMonoid (β j)] (f : ∀ i, Nontrivial (α i) → κ) (g : ∀ j, Nontriv
ial (β j) → ι)
    (F : ∀ i hi, α i →+ β (f i hi)) (G : ∀ j hj, β j →+ α (g j hj))
    (hfg : ∀ i hi hj, g (f i hi) hj = i) (hgf : ∀ j hj hi, f (g j hj) hi = j)
    (hFG : ∀ i hi hj a, hfg i hi hj ▸ G _ hj (F i hi a) = a)
    (hGF : ∀ j hj hi b, hgf j hj hi ▸ F _ hi (G j hj b) = b) :
    (⨁ i, α i) ≃+ ⨁ j, β j where
  toFun x := x.sum fun i a ↦ if ha : a = 0 then 0 else DFinsupp.single (f i ⟨a, 
0, ha⟩) (F _ _ a)
  invFun y := y.sum fun j b ↦ if hb : b = 0 then 0 else DFinsupp.single (g j ⟨b,
 0, hb⟩) (G _ _ b)
  -- The two sorries here are probably doable with the existing machinery, but q
uite painful
  left_inv x := DFinsupp.ext fun i ↦ sorry
  right_inv y := DFinsupp.ext fun j ↦ sorry
  map_add' x₁ x₂ := by
    dsimp
    refine DFinsupp.sum_add_index (by simp) fun i a₁ a₂ ↦ ?_
    split_ifs
    any_goals simp_all
    rw [← DFinsupp.single_add, ← map_add, ‹a₁ + a₂ = 0›, map_zero, DFinsupp.sing
le_zero]

private def directSumNeZeroMulEquiv (ι : Type) [DecidableEq ι] (p : ι → ℕ) (n : 
ι → ℕ) :
    (⨁ i : {i // n i ≠ 0}, ZMod (p i ^ n i)) ≃+ ⨁ i, ZMod (p i ^ n i) :=
  DirectSum.congr
    (fun i _ ↦ i)
    (fun j hj ↦ ⟨j, fun h ↦ by simp [h, pow_zero, zmod_nontrivial] at hj⟩)
    (fun i _ ↦ AddMonoidHom.id _)
    (fun j _ ↦ AddMonoidHom.id _)
    (fun i hi hj ↦ rfl)
    (fun j hj hi ↦ rfl)
    (fun i hi hj a ↦ rfl)
    (fun j hj hi a ↦ rfl)
-/
private def directSumNeZeroMulHom {ι : Type} [DecidableEq ι] (p : ι → ℕ) (n : ι → ℕ) :
    (⨁ i : {i // n i ≠ 0}, ZMod (p i ^ n i)) →+ ⨁ i, ZMod (p i ^ n i) :=
  DirectSum.toAddMonoid fun i ↦ DirectSum.of (fun i ↦ ZMod (p i ^ n i)) i
/-
**directSumNeZeroMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def directSumNeZeroMulEquiv (ι : Type) [DecidableEq ι] (p : ι → ℕ) (n : ι → ℕ) :
    (⨁ i : {i // n i ≠ 0}, ZMod (p i ^ n i)) ≃+ ⨁ i, ZMod (p i ^ n i) where
  toFun := directSumNeZeroMulHom p n
  invFun := DirectSum.toAddMonoid fun i ↦
    if h : n i = 0 then 0 else DirectSum.of (fun j : {i // n i ≠ 0} ↦ ZMod (p j ^ n j)) ⟨i, h⟩
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [directSumNeZeroMulHom, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of,
        dif_neg i.prop]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero]
    | of i x =>
      rw [DirectSum.toAddMonoid_of]
      split_ifs with h
      · simp [(ZMod.subsingleton_iff.2 <| by rw [h, pow_zero]).elim x 0]
      · simp_rw [directSumNeZeroMulHom, DirectSum.toAddMonoid_of]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_add' := map_add (directSumNeZeroMulHom p n)

universe u

namespace Module

variable (M : Type u)

/-
**Module.finite_of_fg_torsion** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finite_of_fg_torsion [AddCommGroup M] [Module Int M] [Module.Finite Int M]
 (hM : Module.IsTorsion Int M) : _root_.Finite M
参数：hM : Module.IsTorsion Int M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.equiv_directSum_of_isTorsion`：equiv_directSum_of_isTorsion [h' : 
Module.Finite R M] (hM : Module.IsTorsion R M) : exists (ι : Type u) (_ : Fintyp
e ι) (p : ι -> R) (_ : fo…
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natAbs_ne_zero`：∀ {a : ℤ}, a.natAbs ≠ 0 ↔ a ≠ 0
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem finite_of_fg_torsion [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]
    (hM : Module.IsTorsion ℤ M) : _root_.Finite M := by
  rcases Module.equiv_directSum_of_isTorsion hM with ⟨ι, _, p, h, e, ⟨l⟩⟩
  have : ∀ i : ι, NeZero (p i ^ e i).natAbs := fun i =>
    ⟨Int.natAbs_ne_zero.mpr <| pow_ne_zero (e i) (h i).ne_zero⟩
  have : ∀ i : ι, _root_.Finite <| ℤ ⧸ Submodule.span ℤ {p i ^ e i} := fun i =>
    Finite.of_equiv _ (p i ^ e i).quotientSpanEquivZMod.symm.toEquiv
  have : _root_.Finite (⨁ i, ℤ ⧸ (Submodule.span ℤ {p i ^ e i} : Submodule ℤ ℤ)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  exact Finite.of_equiv _ l.symm.toEquiv

end Module

variable (G : Type u)

namespace AddCommGroup

variable [AddCommGroup G]

/-- **Structure theorem of finitely generated abelian groups** : Any finitely generated abelian
group is the product of a power of `ℤ` and a direct sum of some `ZMod (p i ^ e i)` for some
prime powers `p i ^ e i`. -/
/-
**AddCommGroup.equiv_free_prod_directSum_zmod** 是 Mathlib 中的一个定理，位于命名空间 `AddComm
Group`。
形式化陈述：equiv_free_prod_directSum_zmod [hG : AddGroup.FG G] : exists (n : Nat) (ι 
: Type) (_ : Fintype ι) (p : ι -> Nat) (_ : forall i, Nat.Prime <| p i) (e : ι -
> Nat), Nonempty G ≃+ (Fin n ->₀ Int) × ⨁ i : ι, ZMod (p i ^ e i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.equiv_free_prod_directSum`：equiv_free_prod_directSum [h' : Module
.Finite R M] : exists (n : Nat) (ι : Type u) (_ : Fintype ι) (p : ι -> R) (_ : f
orall i, Irreducible <…
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Finite.iff_addGroup_fg`：iff_addGroup_fg {G : Type*} [AddCommGroup
 G] : Module.Finite Int G ↔ AddGroup.FG G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.prime_iff_natAbs_prime`：prime_iff_natAbs_prime {k : Int} : Prime k ↔
 Nat.Prime k.natAbs
· 使用定理 `irreducible_iff_prime`：irreducible_iff_prime [DecompositionMonoid M] {a 
: M} : Irreducible a ↔ Prime a
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `UniqueFactorizationMonoid.instDecompositionMonoid`：∀ {α : Type u_1} [ins
t : CommMonoidWithZero α] [UniqueFactorizationMonoid α], DecompositionMonoid α
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Int.natAbs_pow`：∀ (n : ℤ) (k : ℕ), (n ^ k).natAbs = n.natAbs ^ k

--- 原说明 ---
**Structure theorem of finitely generated abelian groups** : Any finitely genera
ted abelian
group is the product of a power of `ℤ` and a direct sum of some `ZMod (p i ^ e i
)` for some
prime powers `p i ^ e i`.
-/
theorem equiv_free_prod_directSum_zmod [hG : AddGroup.FG G] :
    ∃ (n : ℕ) (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime <| p i) (e : ι → ℕ),
      Nonempty <| G ≃+ (Fin n →₀ ℤ) × ⨁ i : ι, ZMod (p i ^ e i) := by
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ :=
    @Module.equiv_free_prod_directSum _ _ _ _ _ _ _ (Module.Finite.iff_addGroup_fg.mpr hG)
  refine ⟨n, ι, fι, fun i => (p i).natAbs, fun i => ?_, e, ⟨?_⟩⟩
  · rw [← Int.prime_iff_natAbs_prime, ← irreducible_iff_prime]; exact hp i
  exact
    f.toAddEquiv.trans
      ((AddEquiv.refl _).prodCongr <|
        DFinsupp.mapRange.addEquiv fun i =>
          ((Int.quotientSpanEquivZMod _).trans <|
              ZMod.ringEquivCongr <| (p i).natAbs_pow _).toAddEquiv)

/-- **Structure theorem of finite abelian groups** : Any finite abelian group is a direct sum of
some `ZMod (p i ^ e i)` for some prime powers `p i ^ e i`. -/
/-
**AddCommGroup.equiv_directSum_zmod_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `AddComm
Group`。
形式化陈述：equiv_directSum_zmod_of_finite [Finite G] : exists (ι : Type) (_ : Fintype
 ι) (p : ι -> Nat) (_ : forall i, Nat.Prime <| p i) (e : ι -> Nat), Nonempty G ≃
+ ⨁ i : ι, ZMod (p i ^ e i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `AddCommGroup.equiv_free_prod_directSum_zmod`：equiv_free_prod_directSum_z
mod [hG : AddGroup.FG G] : exists (n : Nat) (ι : Type) (_ : Fintype ι) (p : ι ->
 Nat) (_ : forall i, Nat.Prime <|…
· 使用定理 `AddGroup.fg_of_finite`：∀ {G : Type u_3} [inst : AddGroup G] [Finite G], 
AddGroup.FG G
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Fintype.false`：∀ {α : Type u_1} [Infinite α] (_h : Fintype α), False
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b

--- 原说明 ---
**Structure theorem of finite abelian groups** : Any finite abelian group is a d
irect sum of
some `ZMod (p i ^ e i)` for some prime powers `p i ^ e i`.
-/
theorem equiv_directSum_zmod_of_finite [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime <| p i) (e : ι → ℕ),
      Nonempty <| G ≃+ ⨁ i : ι, ZMod (p i ^ e i) := by
  cases nonempty_fintype G
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := equiv_free_prod_directSum_zmod G
  rcases n with - | n
  · have : Unique (Fin Nat.zero →₀ ℤ) :=
      { uniq := by subsingleton }
    exact ⟨ι, fι, p, hp, e, ⟨f.trans AddEquiv.uniqueProd⟩⟩
  · have := @Fintype.prodLeft _ _ _ (Fintype.ofEquiv G f.toEquiv) _
    exact
      (Fintype.ofSurjective (fun f : Fin n.succ →₀ ℤ => f 0) fun a =>
            ⟨Finsupp.single 0 a, Finsupp.single_eq_same⟩).false.elim

/-- **Structure theorem of finite abelian groups** : Any finite abelian group is a direct sum of
some `ZMod (n i)` for some natural numbers `n i > 1`. -/
/-
**AddCommGroup.equiv_directSum_zmod_of_finite'** 是 Mathlib 中的一个引理，位于命名空间 `AddCom
mGroup`。
形式化陈述：equiv_directSum_zmod_of_finite' (G : Type*) [AddCommGroup G] [Finite G] : 
exists (ι : Type) (_ : Fintype ι) (n : ι -> Nat), (forall i, 1 < n i) ∧ Nonempty
 (G ≃+ ⨁ i, ZMod (n i))
参数：G : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.equiv_directSum_zmod_of_finite`：equiv_directSum_zmod_of_fin
ite [Finite G] : exists (ι : Type) (_ : Fintype ι) (p : ι -> Nat) (_ : forall i,
 Nat.Prime <| p i) (e : ι -> Nat)…
· 使用定理 `one_lt_pow₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preo
rder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   1 < a → ∀ {n : ℕ}, n ≠ 
0…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p

--- 原说明 ---
**Structure theorem of finite abelian groups** : Any finite abelian group is a d
irect sum of
some `ZMod (n i)` for some natural numbers `n i > 1`.
-/
lemma equiv_directSum_zmod_of_finite' (G : Type*) [AddCommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
      (∀ i, 1 < n i) ∧ Nonempty (G ≃+ ⨁ i, ZMod (n i)) := by
  classical
  obtain ⟨ι, hι, p, hp, n, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  refine ⟨{i : ι // n i ≠ 0}, inferInstance, fun i ↦ p i ^ n i, ?_,
    ⟨e.trans (directSumNeZeroMulEquiv ι _ _).symm⟩⟩
  rintro ⟨i, hi⟩
  exact one_lt_pow₀ (hp _).one_lt hi
/-
**AddCommGroup.finite_of_fg_isAddTorsion** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup
`。
形式化陈述：finite_of_fg_isAddTorsion [hG' : AddGroup.FG G] (hG : IsAddTorsion G) : Fi
nite G
参数：hG : IsAddTorsion G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finite_of_fg_torsion`：finite_of_fg_torsion [AddCommGroup M] [Modu
le Int M] [Module.Finite Int M] (hM : Module.IsTorsion Int M) : _root_.Finite M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Finite.iff_addGroup_fg`：iff_addGroup_fg {G : Type*} [AddCommGroup
 G] : Module.Finite Int G ↔ AddGroup.FG G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isAddTorsion_iff_isTorsion_int`：isAddTorsion_iff_isTorsion_int [AddCommG
roup M] : IsAddTorsion M ↔ Module.IsTorsion Int M
-/
theorem finite_of_fg_isAddTorsion [hG' : AddGroup.FG G] (hG : IsAddTorsion G) : Finite G :=
  @Module.finite_of_fg_torsion _ _ _ (Module.Finite.iff_addGroup_fg.mpr hG') <|
    isAddTorsion_iff_isTorsion_int.mp hG

@[deprecated (since := "2026-07-01")] alias finite_of_fg_torsion := finite_of_fg_isAddTorsion

end AddCommGroup

namespace CommGroup

@[to_additive existing]
/-
**CommGroup.finite_of_fg_isMulTorsion** 是 Mathlib 中的一个定理，位于命名空间 `CommGroup`。
形式化陈述：finite_of_fg_isMulTorsion [CommGroup G] [Group.FG G] (hG : IsMulTorsion G)
 : Finite G
参数：hG : IsMulTorsion G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `AddCommGroup.finite_of_fg_isAddTorsion`：finite_of_fg_isAddTorsion [hG' :
 AddGroup.FG G] (hG : IsAddTorsion G) : Finite G
-/
theorem finite_of_fg_isMulTorsion [CommGroup G] [Group.FG G] (hG : IsMulTorsion G) : Finite G :=
  @Finite.of_equiv _ _ (AddCommGroup.finite_of_fg_isAddTorsion (Additive G) hG) Multiplicative.ofAdd

@[deprecated (since := "2026-07-01")] alias finite_of_fg_torsion := finite_of_fg_isMulTorsion

/-- The **Structure Theorem For Finite Abelian Groups** in a multiplicative version:
A finite abelian group `G` is isomorphic to a finite product of finite cyclic groups. -/
/-
**CommGroup.equiv_prod_multiplicative_zmod_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `
CommGroup`。
形式化陈述：equiv_prod_multiplicative_zmod_of_finite (G : Type*) [CommGroup G] [Finite
 G] : exists (ι : Type) (_ : Fintype ι) (n : ι -> Nat), (forall (i : ι), 1 < n i
) ∧ Nonempty (G ≃* ((i : ι) -> Multiplicative (ZMod (n i))))
参数：G : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AddCommGroup.equiv_directSum_zmod_of_finite'`：equiv_directSum_zmod_of_fi
nite' (G : Type*) [AddCommGroup G] [Finite G] : exists (ι : Type) (_ : Fintype ι
) (n : ι -> Nat), (forall i, 1 < n…
· 使用定理 `instFiniteAdditive`：∀ {α : Type u} [Finite α], Finite (Additive α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The **Structure Theorem For Finite Abelian Groups** in a multiplicative version:
A finite abelian group `G` is isomorphic to a finite product of finite cyclic gr
oups.
-/
theorem equiv_prod_multiplicative_zmod_of_finite (G : Type*) [CommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
       (∀ (i : ι), 1 < n i) ∧ Nonempty (G ≃* ((i : ι) → Multiplicative (ZMod (n i)))) := by
  obtain ⟨ι, inst, n, h₁, h₂⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' (Additive G)
  exact ⟨ι, inst, n, h₁, ⟨MulEquiv.toAdditive.symm <| h₂.some.trans <|
    (DirectSum.addEquivProd _).trans (MulEquiv.piMultiplicative _).toAdditiveRight⟩⟩

/-- The **Structure theorem of finitely generated abelian groups** in a multiplicative version:
Any finitely generated abelian group is the product of a power of `ℤ`
and a direct product of some `ZMod (p i ^ e i)` for some prime powers `p i ^ e i`. -/
/-
**CommGroup.equiv_free_prod_prod_multiplicative_zmod** 是 Mathlib 中的一个定理，位于命名空间 `
CommGroup`。
形式化陈述：equiv_free_prod_prod_multiplicative_zmod (G : Type*) [CommGroup G] [hG : G
roup.FG G] : exists (ι j : Type) (_ : Fintype ι) (_ : Fintype j) (p : ι -> Nat) 
(_ : forall i, Nat.Prime <| p i) (e : ι -> Nat), Nonempty G ≃* (j -> Multiplicat
ive Int) × ((i : ι) -> Multiplicative (ZMod (p i ^ e i)))
参数：G : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.equiv_free_prod_directSum_zmod`：equiv_free_prod_directSum_z
mod [hG : AddGroup.FG G] : exists (n : Nat) (ι : Type) (_ : Fintype ι) (p : ι ->
 Nat) (_ : forall i, Nat.Prime <|…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The **Structure theorem of finitely generated abelian groups** in a multiplicati
ve version:
Any finitely generated abelian group is the product of a power of `ℤ`
and a direct product of some `ZMod (p i ^ e i)` for some prime powers `p i ^ e i
`.
-/
theorem equiv_free_prod_prod_multiplicative_zmod (G : Type*) [CommGroup G] [hG : Group.FG G] :
    ∃ (ι j : Type) (_ : Fintype ι) (_ : Fintype j) (p : ι → ℕ)
    (_ : ∀ i, Nat.Prime <| p i) (e : ι → ℕ),
      Nonempty <| G ≃* (j → Multiplicative ℤ) × ((i : ι) → Multiplicative (ZMod (p i ^ e i))) := by
  obtain ⟨n, ι, inst, x, p, e, equiv⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Additive G)
  exact ⟨ι, Fin n, inst, inferInstance, x, p, e, ⟨MulEquiv.toAdditive.symm <| equiv.some.trans <|
    ((Finsupp.addEquivFunOnFinite.trans <| ((AddEquiv.piAdditive _).trans <|
        (AddEquiv.additiveMultiplicative ℤ).arrowCongr (Equiv.refl _)).symm).prodCongr
          (DirectSum.addEquivProd _ )).trans <| (AddEquiv.prodAdditive _ _).symm⟩⟩

end CommGroup

namespace Subgroup

@[to_additive]
/-
**Subgroup.finiteIndex_range_powMonoidHom_of_fg** 是 Mathlib 中的一个引理，位于命名空间 `Subgr
oup`。
形式化陈述：finiteIndex_range_powMonoidHom_of_fg (A : Type*) [CommGroup A] [Group.FG A
] {n : Nat} (hn : n != 0) : (powMonoidHom (α
参数：A : Type*；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.finiteIndex_iff_finite_quotient`：finiteIndex_iff_finite_quotien
t : FiniteIndex H ↔ Finite (G ⧸ H)
· 使用定理 `CommGroup.finite_of_fg_isMulTorsion`：finite_of_fg_isMulTorsion [CommGrou
p G] [Group.FG G] (hG : IsMulTorsion G) : Finite G
· 使用引理 `CommGroup.isMulTorsion_quotient_range_powMonoidHom`：isMulTorsion_quotien
t_range_powMonoidHom {n : Nat} (hn : n != 0) : IsMulTorsion (G ⧸ (powMonoidHom (
α
-/
lemma finiteIndex_range_powMonoidHom_of_fg (A : Type*) [CommGroup A] [Group.FG A] {n : ℕ}
    (hn : n ≠ 0) :
    (powMonoidHom (α := A) n).range.FiniteIndex :=
  finiteIndex_iff_finite_quotient.mpr <| CommGroup.finite_of_fg_isMulTorsion _ <|
    CommGroup.isMulTorsion_quotient_range_powMonoidHom A hn

@[to_additive]
/-
**Subgroup.isFiniteRelIndex_map_powMonoidHom_of_fg** 是 Mathlib 中的一个引理，位于命名空间 `Su
bgroup`。
形式化陈述：isFiniteRelIndex_map_powMonoidHom_of_fg {A : Type*} [CommGroup A] {B : Sub
group A} (hB : B.FG) {n : Nat} (hn : n != 0) : .IsFiniteRelIndex B
参数：hB : B.FG；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.isFiniteRelIndex_iff_finiteIndex`：isFiniteRelIndex_iff_finiteIn
dex : H.IsFiniteRelIndex K ↔ (H.subgroupOf K).FiniteIndex
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `powMonoidHom_apply`：∀ {α : Type u_1} [inst : CommMonoid α] (n : ℕ) (x : 
α), (powMonoidHom n) x = x ^ n
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Group.fg_iff_subgroup_fg`：Group.fg_iff_subgroup_fg (H : Subgroup G) : Gr
oup.FG H ↔ H.FG
· 使用引理 `Subgroup.finiteIndex_range_powMonoidHom_of_fg`：finiteIndex_range_powMono
idHom_of_fg (A : Type*) [CommGroup A] [Group.FG A] {n : Nat} (hn : n != 0) : (po
wMonoidHom (α
-/
lemma isFiniteRelIndex_map_powMonoidHom_of_fg {A : Type*} [CommGroup A] {B : Subgroup A}
    (hB : B.FG) {n : ℕ} (hn : n ≠ 0) :
    B.map (powMonoidHom (α := A) n) |>.IsFiniteRelIndex B := by
  rw [isFiniteRelIndex_iff_finiteIndex]
  have : (map (powMonoidHom (α := A) n) B).subgroupOf B = (powMonoidHom (α := B) n).range := by
    ext1
    simp [mem_subgroupOf, Subtype.ext_iff]
  rw [this]
  have := (Group.fg_iff_subgroup_fg B).mpr hB
  exact finiteIndex_range_powMonoidHom_of_fg B hn

end Subgroup

namespace Submodule

variable {R K M : Type*} [CommRing R] [CommRing K] [Algebra R K] [Module.Finite ℤ R]
  [AddCommGroup M] [Module R M]

/-
**Submodule.fg_toAddSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：fg_toAddSubgroup {A : Submodule R M} (hfg : A.FG) : A.toAddSubgroup.FG
参数：hfg : A.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubgroup.toIntSubmodule_toAddSubgroup`：AddSubgroup.toIntSubmodule_toA
ddSubgroup (S : AddSubgroup M) : S.toIntSubmodule.toAddSubgroup = S
· 使用定理 `Submodule.fg_iff_addSubgroup_fg`：fg_iff_addSubgroup_fg {G : Type*} [AddC
ommGroup G] (P : Submodule Int G) : P.FG ↔ P.toAddSubgroup.FG
· 使用定理 `Submodule.FG.restrictScalars`：∀ {R : Type u_1} [inst : Semiring R] {M : 
Type u_2} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {A : Type u_
3} [inst_3 : Semir…
-/
lemma fg_toAddSubgroup {A : Submodule R M} (hfg : A.FG) : A.toAddSubgroup.FG := by
  rw [← AddSubgroup.toIntSubmodule_toAddSubgroup A.toAddSubgroup, ← fg_iff_addSubgroup_fg]
  exact FG.restrictScalars hfg

open AddSubgroup in
/-- If `A` and `B` are two `R`-submodules of the `R`-algebra `M`, where `R` is finitely generated
as a `ℤ`-module, `A` is finitely generated, and `B` contains `n • A`, then `B` has finite
relative index in `A`. -/
/-
**Submodule.isFiniteRelIndex_of_map_linearMapMulLeft_le** 是 Mathlib 中的一个引理，位于命名空
间 `Submodule`。
形式化陈述：isFiniteRelIndex_of_map_linearMapMulLeft_le {A B : Submodule R K} {n : Nat
} (hn : n != 0) (hfg : A.FG) (h : A.map (LinearMap.mulLeft R (n : K)) <= B) : B.
toAddSubgroup.IsFiniteRelIndex A.toAddSubgroup
参数：hn : n != 0；hfg : A.FG；h : A.map (LinearMap.mulLeft R (n : K)) <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Submodule.fg_toAddSubgroup`：fg_toAddSubgroup {A : Submodule R M} (hfg : 
A.FG) : A.toAddSubgroup.FG
· 使用定理 `AddSubgroup.isFiniteRelIndex_map_nsmulAddMonoidHom_of_fg`：∀ {A : Type u_
1} [inst : AddCommGroup A] {B : AddSubgroup A},   B.FG → ∀ {n : ℕ}, n ≠ 0 → (Add
Subgroup.map (nsmulAddMonoidHom n) B).IsFinite…
· 使用定理 `AddSubgroup.isFiniteRelIndex_of_le_left`：∀ {G : Type u_1} [inst : AddGro
up G] {H K : AddSubgroup G} (L : AddSubgroup G) [H.IsFiniteRelIndex L],   H ≤ K 
→ K.IsFiniteRelIndex L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmulAddMonoidHom_apply`：∀ {α : Type u_1} [inst : AddCommMonoid α] (n : 
ℕ) (x : α), (nsmulAddMonoidHom n) x = n • x
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a

--- 原说明 ---
If `A` and `B` are two `R`-submodules of the `R`-algebra `M`, where `R` is finit
ely generated
as a `ℤ`-module, `A` is finitely generated, and `B` contains `n • A`, then `B` h
as finite
relative index in `A`.
-/
lemma isFiniteRelIndex_of_map_linearMapMulLeft_le {A B : Submodule R K} {n : ℕ} (hn : n ≠ 0)
    (hfg : A.FG) (h : A.map (LinearMap.mulLeft R (n : K)) ≤ B) :
    B.toAddSubgroup.IsFiniteRelIndex A.toAddSubgroup := by
  have := fg_toAddSubgroup hfg
  have := isFiniteRelIndex_map_nsmulAddMonoidHom_of_fg this hn
  refine isFiniteRelIndex_of_le_left (H := A.toAddSubgroup.map (nsmulAddMonoidHom n))
    A.toAddSubgroup ?_
  rw [SetLike.le_def] at h ⊢
  simpa using h

end Submodule

