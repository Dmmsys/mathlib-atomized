/-
Copyright (c) 2024 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Divisibility.Prod
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Localizing a product of commutative rings

## Main Result

* `bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom`: the canonical map from a
    localization of a finite product of rings `R i` at a monoid `M` to the direct product of
    localizations `R i` at the projection of `M` onto each corresponding factor is bijective.

## Implementation notes

See `Mathlib/RingTheory/Localization/Defs.lean` for a design overview.

## Tags
localization, commutative ring
-/

public section

namespace IsLocalization

variable {ι : Type*} (R S : ι → Type*)
  [Π i, CommSemiring (R i)] [Π i, CommSemiring (S i)] [Π i, Algebra (R i) (S i)]

/-- If `S i` is a localization of `R i` at the submonoid `M i` for each `i`,
then `Π i, S i` is a localization of `Π i, R i` at the product submonoid. -/
/-
**IsLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S i` is a localization of `R i` at the submonoid `M i` for each `i`,
then `Π i, S i` is a localization of `Π i, R i` at the product submonoid.
-/
instance (M : Π i, Submonoid (R i)) [∀ i, IsLocalization (M i) (S i)] :
    IsLocalization (.pi .univ M) (Π i, S i) where
  map_units m := Pi.isUnit_iff.mpr fun i ↦ map_units _ ⟨m.1 i, m.2 i ⟨⟩⟩
  surj z := by
    choose rm h using fun i ↦ surj (M := M i) (z i)
    exact ⟨(fun i ↦ (rm i).1, ⟨_, fun i _ ↦ (rm i).2.2⟩), funext h⟩
  exists_of_eq {x y} eq := by
    choose c hc using fun i ↦ exists_of_eq (M := M i) (congr_fun eq i)
    exact ⟨⟨_, fun i _ ↦ (c i).2⟩, funext hc⟩

variable (S' : Type*) [CommSemiring S'] [Algebra (Π i, R i) S'] (M : Submonoid (Π i, R i))
/-
**IsLocalization.iff_map_piEvalRingHom** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization
`。
形式化陈述：iff_map_piEvalRingHom [Finite ι] : IsLocalization M S' ↔ IsLocalization (.
pi .univ fun i => M.map (Pi.evalRingHom R i)) S'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.iff_of_le_of_exists_dvd`：iff_of_le_of_exists_dvd (N : Sub
monoid R) (h₁ : M <= N) (h₂ : forall n in N, exists m in M, n ∣ m) : IsLocalizat
ion M S ↔ IsLocalization N S
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `prod_mem`：prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidCl
ass B M] {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S)…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pi_dvd_iff`：pi_dvd_iff {x y : forall i, G i} : x ∣ y ↔ forall i, x i ∣ y
 i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.prod_apply`：Fintype.prod_apply {α : Type*} {M : α -> Type*} [Fin
type ι] [forall a, CommMonoid (M a)] (a : α) (g : ι -> forall a, M a) : (∏ c, g 
c) a = ∏…
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Eq.dvd`：∀ {α : Type u_1} [inst : Monoid α] {a b : α}, a = b → a ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem iff_map_piEvalRingHom [Finite ι] :
    IsLocalization M S' ↔ IsLocalization (.pi .univ fun i ↦ M.map (Pi.evalRingHom R i)) S' :=
  iff_of_le_of_exists_dvd M _ (fun m hm i _ ↦ ⟨m, hm, rfl⟩) fun n hn ↦ by
    choose m mem eq using hn
    have := Fintype.ofFinite ι
    refine ⟨∏ i, m i ⟨⟩, prod_mem fun i _ ↦ mem i _, pi_dvd_iff.mpr fun i ↦ ?_⟩
    rw [Fintype.prod_apply]
    exact (eq i ⟨⟩).symm.dvd.trans (Finset.dvd_prod_of_mem _ <| Finset.mem_univ _)

variable [∀ i, IsLocalization (M.map (Pi.evalRingHom R i)) (S i)]

/-- Let `M` be a submonoid of a direct product of commutative rings `R i`, and let `M' i` denote
the projection of `M` onto each corresponding factor. Given a ring homomorphism from the direct
product `Π i, R i` to the product of the localizations of each `R i` at `M' i`, every `y : M`
maps to a unit under this homomorphism. -/
/-
**IsLocalization.isUnit_piRingHom_algebraMap_comp_piEvalRingHom** 是 Mathlib 中的一个
引理，位于命名空间 `IsLocalization`。
形式化陈述：isUnit_piRingHom_algebraMap_comp_piEvalRingHom (y : M) : IsUnit ((RingHom.
pi fun i => (algebraMap (R i) (S i)).comp (Pi.evalRingHom R i)) y)
参数：y : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Pi.isUnit_iff`：Pi.isUnit_iff : IsUnit x ↔ forall i, IsUnit (x i)
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
Let `M` be a submonoid of a direct product of commutative rings `R i`, and let `
M' i` denote
the projection of `M` onto each corresponding factor. Given a ring homomorphism 
from the direct
product `Π i, R i` to the product of the localizations of each `R i` at `M' i`, 
every `y : M`
maps to a unit under this homomorphism.
-/
lemma isUnit_piRingHom_algebraMap_comp_piEvalRingHom (y : M) :
    IsUnit ((RingHom.pi fun i ↦ (algebraMap (R i) (S i)).comp (Pi.evalRingHom R i)) y) :=
  Pi.isUnit_iff.mpr fun i ↦ map_units _ (⟨y.1 i, y, y.2, rfl⟩ : M.map (Pi.evalRingHom R i))

/-- Let `M` be a submonoid of a direct product of commutative rings `R i`, and let `M' i` denote
the projection of `M` onto each factor. Then the canonical map from the localization of the direct
product `Π i, R i` at `M` to the direct product of the localizations of each `R i` at `M' i`
is bijective. -/
/-
**IsLocalization.bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom** 是 Math
lib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom [IsLocalization M S
'] [Finite ι] : Function.Bijective (lift (S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalization.iff_map_piEvalRingHom`：iff_map_piEvalRingHom [Finite ι] :
 IsLocalization M S' ↔ IsLocalization (.pi .univ fun i => M.map (Pi.evalRingHom 
R i)) S'
· 使用定理 `IsLocalization.instForallPiUniv`：∀ {ι : Type u_1} (R : ι → Type u_2) (S 
: ι → Type u_3) [inst : (i : ι) → CommSemiring (R i)]   [inst_1 : (i : ι) → Comm
Semiring (S i)] [inst…
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
· 使用定理 `Submonoid.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (f : M ≃* N) 
(K : Submonoid M) : K.map f = K.comap f.symm

--- 原说明 ---
Let `M` be a submonoid of a direct product of commutative rings `R i`, and let `
M' i` denote
the projection of `M` onto each factor. Then the canonical map from the localiza
tion of the direct
product `Π i, R i` at `M` to the direct product of the localizations of each `R 
i` at `M' i`
is bijective.
-/
theorem bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom [IsLocalization M S'] [Finite ι] :
    Function.Bijective (lift (S := S') (isUnit_piRingHom_algebraMap_comp_piEvalRingHom R S M)) :=
  have := (iff_map_piEvalRingHom R (Π i, S i) M).mpr inferInstance
  (ringEquivOfRingEquiv (M := M) (T := M) _ _ (.refl _) <|
    Submonoid.map_equiv_eq_comap_symm _ _).bijective

open Function Ideal

include M in
variable {R} in
/-
**IsLocalization.surjective_piRingHom_algebraMap_comp_piEvalRingHom** 是 Mathlib 
中的一个引理，位于命名空间 `IsLocalization`。
形式化陈述：surjective_piRingHom_algebraMap_comp_piEvalRingHom [forall i, Ring.KrullDi
mLE 0 (R i)] [forall i, IsLocalRing (R i)] : Surjective (RingHom.pi (fun i => (a
lgebraMap (R i) (S i)).comp (Pi.evalRingHom R i)))
参数：R i；R i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Function.Surjective.piMap`：∀ {ι : Sort u_1} {α : ι → Sort u_2} {β : ι → 
Sort u_3} {f : (i : ι) → α i → β i},   (∀ (i : ι), Function.Surjective (f i)) → 
Function.Surjec…
· 使用定理 `Function.surjective_to_subsingleton`：surjective_to_subsingleton [na : No
nempty α] [Subsingleton β] (f : α -> β) : Surjective f
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
-/
lemma surjective_piRingHom_algebraMap_comp_piEvalRingHom
    [∀ i, Ring.KrullDimLE 0 (R i)] [∀ i, IsLocalRing (R i)] :
    Surjective (RingHom.pi (fun i ↦ (algebraMap (R i) (S i)).comp (Pi.evalRingHom R i))) := by
  apply Surjective.piMap (fun i ↦ ?_)
  by_cases h₀ : (0 : R i) ∈ (M.map (Pi.evalRingHom R i))
  · have := uniqueOfZeroMem h₀ (S := (S i))
    exact surjective_to_subsingleton (algebraMap (R i) (S i))
  · exact (IsLocalization.atUnits _ _ (by simpa)).surjective

variable {R} in
/-- Let `M` be a submonoid of a direct product of commutative rings `R i`.
If each `R i` has maximal nilradical then the direct product `∏ R i` surjects onto the
localization of `∏ R i` at `M`. -/
/-
**IsLocalization.algebraMap_pi_surjective_of_isLocalization** 是 Mathlib 中的一个引理，位
于命名空间 `IsLocalization`。
形式化陈述：algebraMap_pi_surjective_of_isLocalization [forall i, Ring.KrullDimLE 0 (R
 i)] [forall i, IsLocalRing (R i)] [IsLocalization M S'] [Finite ι] : Surjective
 (algebraMap (Π i, R i) S')
参数：R i；R i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `IsLocalization.isUnit_piRingHom_algebraMap_comp_piEvalRingHom`：isUnit_pi
RingHom_algebraMap_comp_piEvalRingHom (y : M) : IsUnit ((RingHom.pi fun i => (al
gebraMap (R i) (S i)).comp (Pi.evalRingHom R i)) y)
· 使用引理 `IsLocalization.surjective_piRingHom_algebraMap_comp_piEvalRingHom`：surje
ctive_piRingHom_algebraMap_comp_piEvalRingHom [forall i, Ring.KrullDimLE 0 (R i)
] [forall i, IsLocalRing (R i)] : Surjective (RingHom.p…
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `IsLocalization.bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom`：b
ijective_lift_piRingHom_algebraMap_comp_piEvalRingHom [IsLocalization M S'] [Fin
ite ι] : Function.Bijective (lift (S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.lift_eq`：lift_eq (x : R) : lift hg ((algebraMap R S) x) =
 g x

--- 原说明 ---
Let `M` be a submonoid of a direct product of commutative rings `R i`.
If each `R i` has maximal nilradical then the direct product `∏ R i` surjects on
to the
localization of `∏ R i` at `M`.
-/
lemma algebraMap_pi_surjective_of_isLocalization [∀ i, Ring.KrullDimLE 0 (R i)]
    [∀ i, IsLocalRing (R i)] [IsLocalization M S']
    [Finite ι] : Surjective (algebraMap (Π i, R i) S') := by
  intro s
  set S := fun (i : ι) => Localization (M.map (Pi.evalRingHom R i))
  obtain ⟨r, hr⟩ :=
    surjective_piRingHom_algebraMap_comp_piEvalRingHom
    S M ((lift (isUnit_piRingHom_algebraMap_comp_piEvalRingHom R S M)) s)
  refine ⟨r, (bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom R S _ M).injective ?_⟩
  rwa [lift_eq (isUnit_piRingHom_algebraMap_comp_piEvalRingHom R S M) r]

end IsLocalization

